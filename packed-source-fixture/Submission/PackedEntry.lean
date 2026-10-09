import Submission.CompileArchive
import Lean.Elab.Command

namespace FLTCodec
open Lean Elab Command

syntax (name := loadPackedFixture) "load_packed_fixture " str : command

/-- Compile the unchanged fixture module sources and import the resulting
modules into the actual submitted module, rather than retaining a loader-local
environment. This fixture-specific entry must precede local declarations. -/
@[command_elab loadPackedFixture]
unsafe def elabLoadPackedFixture : CommandElab := fun stx => do
  let original ← getEnv
  unless original.constants.map₂.isEmpty do
    throwError "packed entry must precede local declarations"
  let some encoded := stx[1].isStrLit? | throwUnsupportedSyntax
  let input ← IO.ofExcept (decodeBase85 encoded)
  let decoded ← IO.ofExcept (decodeXZ input)
  let files ← IO.ofExcept (decodePAX decoded)
  let codecRoot : System.FilePath := ".lake/build/lib/lean"
  let search ← searchPathRef.get
  searchPathRef.set (codecRoot :: search)
  try
    for (moduleName, fileName) in
        [(`Fixture.ModuleA, "Fixture/ModuleA.lean"),
         (`Fixture.ModuleB, "Fixture/ModuleB.lean")] do
      let some file := files.find? (fun f => f.path == fileName)
        | throwError "missing packed source {fileName}"
      let source ← IO.ofExcept (utf8 file.bytes)
      let objectPath := codecRoot / (fileName.dropEnd 5).toString |>.withExtension "olean"
      let compiled ← compileDecodedModule moduleName fileName source objectPath
      let root := if moduleName == `Fixture.ModuleA then `PackedA.identity else `PackedB.root
      checkNatIdentityType compiled root
      discard <| checkStandardAxioms compiled root
      unless compiled.mainModule == moduleName do throwError "wrong packed main module"
    enableInitializersExecution
    let opts := (← getOptions).setBool `debug.skipKernelTC false |>.setBool `Elab.async false
    let imported ← importModules
      (original.header.imports.push { module := `Fixture.ModuleB }) opts
      (trustLevel := 0) (loadExts := true)
    let imported := imported.setMainModule original.mainModule
      |>.setModulePackage original.getModulePackage?
    unless !imported.contains `PackedA.hidden do throwError "private declaration became public"
    checkNatIdentityType imported `PackedB.root
    discard <| checkStandardAxioms imported `PackedB.root
    setEnv imported
    logInfo m!"PACKED_FIXTURE imported into actual {imported.mainModule} environment; kernel trust 0"
  finally
    searchPathRef.set search

end FLTCodec

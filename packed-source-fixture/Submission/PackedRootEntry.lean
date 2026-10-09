import Submission.CompileArchive
import Lean.Elab.Command

namespace FLTCodec
open Lean Elab Command

/-- Compile the complete original root as its actual module, without writing
an intermediate root olean. Its checked declarations, original imports and
persistent extension states are subsequently emitted by the outer compiler. -/
unsafe def compileDecodedRootSource (moduleName : Name) (fileName source : String)
    (package? : Option PkgId := none)
    : IO Environment := do
  let opts := ({} : Options).setBool `debug.skipKernelTC false |>.setBool `Elab.async false
  enableInitializersExecution
  let some env ← Elab.runFrontend source opts fileName moduleName
    (trustLevel := 0) (oleanFileName? := none)
    (setup? := some { name := moduleName, package? })
    | throw (IO.userError s!"real Lean frontend rejected original root {fileName}")
  return env

syntax (name := loadPackedOriginalRoot) "load_packed_original_root " str : command

@[command_elab loadPackedOriginalRoot]
unsafe def elabLoadPackedOriginalRoot : CommandElab := fun stx => do
  let outer ← getEnv
  unless outer.mainModule == `Submission do throwError "fixture expects actual Submission module"
  unless outer.constants.map₂.isEmpty do throwError "packed root entry must precede local declarations"
  let some encoded := stx[1].isStrLit? | throwUnsupportedSyntax
  let input ← IO.ofExcept (decodeBase85 encoded)
  let decoded ← IO.ofExcept (decodeXZ input)
  let files ← IO.ofExcept (decodePAX decoded)
  let codecRoot : System.FilePath := ".lake/build/lib/lean"
  let finalRootPath := codecRoot / "Submission.olean"
  let rootBefore ← if (← finalRootPath.pathExists) then
      some <$> IO.FS.readBinFile finalRootPath else pure none
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
    let some original := files.find? (fun f => f.path == "Submission.lean")
      | throwError "missing original root source"
    let source ← IO.ofExcept (utf8 original.bytes)
    let rootEnv ← compileDecodedRootSource outer.mainModule "Submission.lean" source
      outer.getModulePackage?
    unless rootEnv.mainModule == outer.mainModule do throwError "original module identity changed"
    unless rootEnv.header.isModule == outer.header.isModule do throwError "original header module mode changed"
    unless !rootEnv.header.imports.any (fun i => i.module == outer.mainModule) do
      throwError "original root contains self import"
    unless !rootEnv.contains `FLTCodec.elabLoadPackedOriginalRoot do
      throwError "loader helper leaked into original root import graph"
    unless !rootEnv.contains `Submission.original_hidden do
      throwError "original private name became public"
    let privateNames := rootEnv.constants.toList.map (fun entry => entry.1.toString)
    unless privateNames.any (fun n => n.startsWith "_private.Submission." &&
        n.endsWith ".Submission.original_hidden_root") do
      throwError "original root private module identity was lost"
    checkNatIdentityType rootEnv `Submission.fermat_last_theorem
    discard <| checkStandardAxioms rootEnv `Submission.fermat_last_theorem
    let rootAfter ← if (← finalRootPath.pathExists) then
        some <$> IO.FS.readBinFile finalRootPath else pure none
    unless rootBefore == rootAfter do
      throwError "nested frontend wrote an intermediate root olean"
    setEnv rootEnv
    logInfo m!"PACKED_ORIGINAL_ROOT actual {rootEnv.mainModule}; original source {original.bytes.size} bytes; no self import; no intermediate root olean; kernel trust 0"
  finally
    searchPathRef.set search

end FLTCodec

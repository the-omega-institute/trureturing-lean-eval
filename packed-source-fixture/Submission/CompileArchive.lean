import Submission.PurePAX
import Lean.Elab.Frontend
import Lean.Util.CollectAxioms

namespace FLTCodec
open Lean

/-- Preserve the actual module header, imports, parser state, private-name
prefix, namespace, options and dynamic syntax using Lean's real frontend.
The source is kept in memory; outputs are confined to the designated .lake.
The official frontend initializer switch is a runtime-only unsafe IO API:
it changes no kernel trust setting. Calls run sequentially in this process.
-/
unsafe def compileDecodedModule (moduleName : Name) (fileName source : String)
    (objectPath : System.FilePath) : IO Environment := do
  let opts := ({} : Options).setBool `debug.skipKernelTC false |>.setBool `Elab.async false
  IO.FS.createDirAll objectPath.parent.get!
  enableInitializersExecution
  let some env ← Elab.runFrontend source opts fileName moduleName (trustLevel := 0)
    (oleanFileName? := some objectPath)
    | throw (IO.userError s!"real Lean frontend rejected {fileName}")
  return env

def checkStandardAxioms (env : Environment) (root : Name) : IO (Array Name) := do
  let ctx : Core.Context := { fileName := "<decoded-prototype>", fileMap := default }
  let state : Core.State := { env }
  let (axioms, _) ← (collectAxioms root : CoreM (Array Name)).toIO ctx state
  for axiomName in axioms do
    if axiomName != `propext && axiomName != `Classical.choice && axiomName != `Quot.sound then
      throw (IO.userError s!"unexpected axiom {axiomName}")
  return axioms

def checkNatIdentityType (env : Environment) (root : Name) : IO Unit := do
  let some info := env.find? root | throw (IO.userError s!"missing {root}")
  let expected := mkForall `n .default (mkConst `Nat)
    (mkApp3 (mkConst `Eq [Level.succ Level.zero]) (mkConst `Nat) (.bvar 0) (.bvar 0))
  unless info.type == expected do throw (IO.userError s!"{root}: exact type differs")

end FLTCodec

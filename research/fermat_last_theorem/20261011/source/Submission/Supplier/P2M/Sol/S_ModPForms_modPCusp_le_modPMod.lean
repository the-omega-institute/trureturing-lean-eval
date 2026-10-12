import Submission.Supplier.Definitions.Def_CuspForm_ModPForms
import Submission.Supplier.P2M.Util

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
namespace P2MW.S_ModPForms_modPCusp_le_modPMod
set_option autoImplicit false

open ModPForms

theorem solution (N' : ℕ) [NeZero N'] (k : ℤ) (F : Type) [Field F] :
    modPCusp N' k F ≤ modPMod N' k F := by
  refine Submodule.span_mono ?_
  rintro φ ⟨f, a, ha, hφ⟩
  exact ⟨(f : ModularForm (CongruenceSubgroup.Gamma0 N') k), a, ha, hφ⟩

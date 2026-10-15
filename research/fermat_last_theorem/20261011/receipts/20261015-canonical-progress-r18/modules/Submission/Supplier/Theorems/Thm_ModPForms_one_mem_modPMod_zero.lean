import Mathlib
import Submission.Supplier.Definitions.Def_CuspForm_ModPForms
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_ModPForms_one_mem_modPMod_zero

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
set_option autoImplicit false

theorem ModPForms.one_mem_modPMod_zero (N : ℕ) (F : Type) [Field F] :
    (1 : PowerSeries F) ∈ ModPForms.modPMod N 0 F := by p2m_exact_reverting @_root_.P2MW.S_ModPForms_one_mem_modPMod_zero.solution

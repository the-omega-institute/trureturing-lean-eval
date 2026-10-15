import Submission.Supplier.Definitions.Def_CuspForm_ModPForms
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_ModPForms_modPMod_eq_bot_of_neg

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
set_option autoImplicit false

theorem ModPForms.modPMod_eq_bot_of_neg (N : ℕ) [NeZero N] (k : ℤ) (hk : k < 0) (F : Type) [Field F] :
    ModPForms.modPMod N k F = ⊥ := by p2m_exact_reverting @_root_.P2MW.S_ModPForms_modPMod_eq_bot_of_neg.solution

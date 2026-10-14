import Mathlib
import Submission.Supplier.Definitions.Def_FLTPrelim_Modularity
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_CuspForm_qCoeff_zero_eq_zero_gamma1

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

open ModularFormClass
theorem CuspForm.qCoeff_zero_eq_zero_gamma1
    {M : ℕ} {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma1 M) k) :
    ModularFormClass.qCoeff f 0 = 0 := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_qCoeff_zero_eq_zero_gamma1.solution

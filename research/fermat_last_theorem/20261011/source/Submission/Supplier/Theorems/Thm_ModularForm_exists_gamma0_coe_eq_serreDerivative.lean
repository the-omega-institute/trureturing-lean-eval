import Submission.Supplier.Definitions.Def_CuspForm_ModPForms
import Mathlib.NumberTheory.ModularForms.Derivative
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_ModularForm_exists_gamma0_coe_eq_serreDerivative

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
set_option autoImplicit false

theorem ModularForm.exists_gamma0_coe_eq_serreDerivative (N' : ℕ) [NeZero N'] (k : ℤ) (f : ModularForm (CongruenceSubgroup.Gamma0 N') k) :
    ∃ g : ModularForm (CongruenceSubgroup.Gamma0 N') (k + 2),
      ⇑g = Derivative.serreDerivative (k : ℂ) ⇑f := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_exists_gamma0_coe_eq_serreDerivative.solution

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_LanglandsTunnell_eq_zero_of_deriv_eq_div_add_mul_of_re_pos_of_isBigO_pow

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

theorem LanglandsTunnell.eq_zero_of_deriv_eq_div_add_mul_of_re_pos_of_isBigO_pow
    (α β : ℂ) (hβ : 0 < β.re) (f : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0))
    (hfeq : ∀ t : ℝ, 0 < t → deriv f t = (α / (t : ℂ) + β) * f t)
    (C : ℝ) (N : ℕ) (hgrowth : ∀ t : ℝ, 1 ≤ t → ‖f t‖ ≤ C * t ^ N) :
    ∀ t : ℝ, 0 < t → f t = 0 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_eq_zero_of_deriv_eq_div_add_mul_of_re_pos_of_isBigO_pow.solution

#print axioms LanglandsTunnell.eq_zero_of_deriv_eq_div_add_mul_of_re_pos_of_isBigO_pow

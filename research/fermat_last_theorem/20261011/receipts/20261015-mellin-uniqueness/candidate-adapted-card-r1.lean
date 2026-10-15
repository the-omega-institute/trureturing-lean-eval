import Submission.Supplier.Definitions.Def_LanglandsTunnell_HonestLDatum
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_LanglandsTunnell_Converse_MellinUniqueness_eq_of_laplace_eq_of_boundedOnStrips

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false
open MeasureTheory

theorem LanglandsTunnell.Converse.MellinUniqueness.eq_of_laplace_eq_of_boundedOnStrips
    (g₁ g₂ : ℝ → ℂ) (hg₁ : Continuous g₁) (hg₂ : Continuous g₂)
    (c : ℝ) (Λ : ℂ → ℂ) (hΛ : Differentiable ℂ Λ) (hb : LDatum.BoundedOnStrips Λ)
    (h₁ : ∀ s : ℂ, c < s.re →
      Integrable (fun t : ℝ => g₁ t * Complex.exp (s * (t : ℂ))) ∧ ∫ t : ℝ, g₁ t * Complex.exp (s * (t : ℂ)) = Λ s)
    (h₂ : ∀ s : ℂ, s.re < -c →
      Integrable (fun t : ℝ => g₂ t * Complex.exp (s * (t : ℂ))) ∧ ∫ t : ℝ, g₂ t * Complex.exp (s * (t : ℂ)) = Λ s) :
    g₁ = g₂ := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_MellinUniqueness_eq_of_laplace_eq_of_boundedOnStrips.solution

#print axioms LanglandsTunnell.Converse.MellinUniqueness.eq_of_laplace_eq_of_boundedOnStrips

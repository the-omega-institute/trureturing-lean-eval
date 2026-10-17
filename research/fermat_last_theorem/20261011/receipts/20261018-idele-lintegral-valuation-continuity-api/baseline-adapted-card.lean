import Submission.Supplier.Definitions.Def_NumberField_IdeleProductMeasure
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_NumberField_Idele_lintegral_mul_prod_ord_sPartMeasure_eq_lintegral_sPartMeasure_empty_mul_prod_tsum

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open MeasureTheory NumberField NumberField.Idele IsDedekindDomain
open scoped ENNReal

theorem NumberField.Idele.lintegral_mul_prod_ord_sPartMeasure_eq_lintegral_sPartMeasure_empty_mul_prod_tsum
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (f : (AdeleRing (𝓞 F) F)ˣ → ℝ≥0∞) (hf : Measurable[ideleBorel F] f)
    (hf1 : ∀ a b : (AdeleRing (𝓞 F) F)ˣ, ((a : AdeleRing (𝓞 F) F)).1 = ((b : AdeleRing (𝓞 F) F)).1 → f a = f b)
    (φ : HeightOneSpectrum (𝓞 F) → ℤ → ℝ≥0∞) :
    (∫⁻ a, f a * ∏ v ∈ S, φ v (ord F v a) ∂(sPartMeasure F S)) =
      (∫⁻ a, f a ∂(sPartMeasure F ∅)) * ∏ v ∈ S, ∑' m : ℤ, φ v m := by p2m_exact_reverting @_root_.P2MW.S_NumberField_Idele_lintegral_mul_prod_ord_sPartMeasure_eq_lintegral_sPartMeasure_empty_mul_prod_tsum.solution

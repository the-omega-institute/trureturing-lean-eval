import Submission.Supplier.Definitions.Def_HaarQuotient
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_HaarQuotient_lintegral_eq_lintegral_lintegral_mul_out

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

theorem HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (f : G → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ g, f g ∂μ = ∫⁻ q, (∫⁻ x, f ((x : G) * q.out) ∂μH) ∂(HaarQuotient.measure μ H μH) := by p2m_exact_reverting @_root_.P2MW.S_HaarQuotient_lintegral_eq_lintegral_lintegral_mul_out.solution

#print axioms HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out

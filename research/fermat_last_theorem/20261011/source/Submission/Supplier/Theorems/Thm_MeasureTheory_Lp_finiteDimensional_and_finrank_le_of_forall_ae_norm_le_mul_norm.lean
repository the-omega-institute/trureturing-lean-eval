import Mathlib
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_MeasureTheory_Lp_finiteDimensional_and_finrank_le_of_forall_ae_norm_le_mul_norm

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

theorem MeasureTheory.Lp.finiteDimensional_and_finrank_le_of_forall_ae_norm_le_mul_norm
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ] {𝕜 : Type*} [RCLike 𝕜]
    (V : Submodule 𝕜 (Lp 𝕜 2 μ)) (C : ℝ)
    (hV : ∀ φ ∈ V, ∀ᵐ x ∂μ, ‖(φ : X → 𝕜) x‖ ≤ C * ‖φ‖) :
    FiniteDimensional 𝕜 V ∧ (Module.finrank 𝕜 V : ℝ) ≤ C ^ 2 * (μ Set.univ).toReal := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_Lp_finiteDimensional_and_finrank_le_of_forall_ae_norm_le_mul_norm.solution

#print axioms MeasureTheory.Lp.finiteDimensional_and_finrank_le_of_forall_ae_norm_le_mul_norm

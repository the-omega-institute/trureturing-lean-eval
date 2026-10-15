import Mathlib
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_NumberField_existsUnique_heightOneSpectrum_forall_map_mem_iff_valuation_le_one

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem NumberField.existsUnique_heightOneSpectrum_forall_map_mem_iff_valuation_le_one
    (K : Type) [Field K] [NumberField K] {Ω : Type} [Field Ω]
    (σ : K →+* Ω) (A : ValuationSubring Ω) (hA : ∃ x : K, σ x ∉ A) :
    ∃! v : HeightOneSpectrum (𝓞 K), ∀ x : K, σ x ∈ A ↔ v.valuation K x ≤ 1 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_existsUnique_heightOneSpectrum_forall_map_mem_iff_valuation_le_one.solution

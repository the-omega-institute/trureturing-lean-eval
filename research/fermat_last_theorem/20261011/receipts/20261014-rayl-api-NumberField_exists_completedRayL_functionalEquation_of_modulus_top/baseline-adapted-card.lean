import Mathlib
import Submission.Supplier.Definitions.Def_NumberField_CompletedRayL
import Submission.Supplier.Definitions.Def_NumberField_RayCharacterData
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_NumberField_exists_completedRayL_functionalEquation_of_modulus_top

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open NumberField NumberField.InfinitePlace Deep.NTSupply

theorem NumberField.exists_completedRayL_functionalEquation_of_modulus_top
    (K : Type) [Field K] [NumberField K]
    (χ : NarrowRayClassGroup K (⊤ : Ideal (𝓞 K)) →* ℂ) (hχ : χ ≠ 1)
    (S : Finset {w : InfinitePlace K // w.IsReal}) (hpar : M4aP2.IsParity K ⊤ χ S) :
    ∃ (W : ℂ) (Λ Λ' : ℂ → ℂ), W ≠ 0 ∧ Differentiable ℂ Λ ∧ Differentiable ℂ Λ' ∧
      (∀ s : ℂ, 1 < s.re →
        Λ s = M4aTorus.completedRayL K ⊤ χ S s ∧
        Λ' s = M4aTorus.completedRayL K ⊤ ((starRingEnd ℂ).toMonoidHom.comp χ) S s) ∧
      (∀ s : ℂ, Λ (1 - s) = W * Λ' s) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_exists_completedRayL_functionalEquation_of_modulus_top.solution

import Mathlib
import Submission.Supplier.Definitions.Def_NumberField_CompletedRayL
import Submission.Supplier.Definitions.Def_NumberField_RayCharacterData
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_NumberField_exists_differentiable_eq_rayClassLSeries_of_ne_one

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open NumberField NumberField.InfinitePlace Deep.NTSupply

theorem NumberField.exists_differentiable_eq_rayClassLSeries_of_ne_one
    (K : Type) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥)
    (χ : NarrowRayClassGroup K 𝔣 →* ℂ) (hχ : χ ≠ 1)
    (S : Finset {w : InfinitePlace K // w.IsReal}) (hpar : M4aP2.IsParity K 𝔣 χ S) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
      ∀ s : ℂ, 1 < s.re → g s = M4aTorus.rayClassLSeries K 𝔣 χ s := by p2m_exact_reverting @_root_.P2MW.S_NumberField_exists_differentiable_eq_rayClassLSeries_of_ne_one.solution

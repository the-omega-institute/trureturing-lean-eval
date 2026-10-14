import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_FullLevelTate_exists_linearEquiv_cancelBaseChange_of_algebraMap_eq

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open scoped TensorProduct

theorem FullLevelTate.exists_linearEquiv_cancelBaseChange_of_algebraMap_eq
    (lam : ℕ) [Fact lam.Prime] (O' : Type) [CommRing O'] [Algebra ℤ_[lam] O']
    (K : Type) [CommRing K] [Algebra O' K] [Algebra ℚ_[lam] K]
    (hOK : ∀ z : ℤ_[lam], algebraMap O' K (algebraMap ℤ_[lam] O' z) = algebraMap ℚ_[lam] K (z : ℚ_[lam]))
    (T : Type) [AddCommMonoid T] [Module ℤ_[lam] T] :
    ∃ e : K ⊗[O'] (O' ⊗[ℤ_[lam]] T) ≃ₗ[K] K ⊗[ℚ_[lam]] (ℚ_[lam] ⊗[ℤ_[lam]] T),
      ∀ (c : K) (a : O') (x : T),
        e (c ⊗ₜ[O'] (a ⊗ₜ[ℤ_[lam]] x)) = (algebraMap O' K a * c) ⊗ₜ[ℚ_[lam]] ((1 : ℚ_[lam]) ⊗ₜ[ℤ_[lam]] x) := by p2m_exact_reverting @_root_.P2MW.S_FullLevelTate_exists_linearEquiv_cancelBaseChange_of_algebraMap_eq.solution

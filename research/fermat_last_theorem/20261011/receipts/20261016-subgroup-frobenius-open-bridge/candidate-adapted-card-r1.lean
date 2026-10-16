import Mathlib
import Submission.Supplier.Definitions.Def_EllipticCurve_FrobeniusTrace
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_Subgroup_exists_prime_isFrobeniusAt_conj_pow_mem_conj_mem_of_isOpen

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
attribute [-instance] FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

theorem Subgroup.exists_prime_isFrobeniusAt_conj_pow_mem_conj_mem_of_isOpen
    (H : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hH : IsOpen (H : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) {M : ℕ} (hM : 0 < M) :
    ∃ (ℓ : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ))
      (τ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (n k : ℕ),
      ℓ.Prime ∧ ¬ ℓ ∣ M ∧ A.LiesOverPrime ℓ ∧ A.IsFrobeniusAt τ ℓ ∧
        g * τ ^ n * g⁻¹ * σ⁻¹ ∈ H ∧ g * τ * g⁻¹ * (σ ^ k)⁻¹ ∈ H := by p2m_exact_reverting @_root_.P2MW.S_Subgroup_exists_prime_isFrobeniusAt_conj_pow_mem_conj_mem_of_isOpen.solution

#print axioms Subgroup.exists_prime_isFrobeniusAt_conj_pow_mem_conj_mem_of_isOpen

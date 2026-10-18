import Mathlib
import Submission.Supplier.Definitions.Def_GaloisRep_Flat
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_HopfAlgebra_ringHom_ratLocalizedAt_eq_of_forall_sub_mem_span_of_natCard_algHom_eq_of_ne_two

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

theorem HopfAlgebra.ringHom_ratLocalizedAt_eq_of_forall_sub_mem_span_of_natCard_algHom_eq_of_ne_two
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (K : Type) (_ : CommRing K) (_ : HopfAlgebra ℤ K) (_ : Algebra.FiniteType ℤ K)
    (_ : Module.Flat ℤ K)
    (hff : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
      Module.Finite (GaloisRep.ratLocalizedAt ℓ) (TensorProduct ℤ (GaloisRep.ratLocalizedAt ℓ) K))
    (hgenq : Nat.card (K →ₐ[ℤ] AlgebraicClosure ℚ) = q)
    (hgal : ∀ (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (ψ : K →ₐ[ℤ] AlgebraicClosure ℚ)
      (k : K), σ (ψ k) = ψ k)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (χ χ' : K →+* GaloisRep.ratLocalizedAt ℓ)
    (h : ∀ k : K, χ k - χ' k ∈ Ideal.span {(ℓ : GaloisRep.ratLocalizedAt ℓ)}) : χ = χ' := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_ringHom_ratLocalizedAt_eq_of_forall_sub_mem_span_of_natCard_algHom_eq_of_ne_two.solution

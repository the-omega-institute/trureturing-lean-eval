import Mathlib
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_ValuationSubring_tensorProduct_exists_primitive_factor

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

open IsLocalRing TensorProduct

theorem ValuationSubring.tensorProduct_exists_primitive_factor
    (K F K' : Type*) [Field K] [CommRing F] [Nontrivial F] [NoZeroDivisors F]
    [Field K'] [Algebra K F] [Algebra K K']
    (A : ValuationSubring K') (hK : ∀ c : K, algebraMap K K' c ∈ A) (σ : A →+* K)
    (hker : RingHom.ker σ = maximalIdeal A)
    (hsec : ∀ c : K, σ ⟨algebraMap K K' c, hK c⟩ = c) :
    letI : Algebra K A := ((algebraMap K K').codRestrict A.toSubring hK).toAlgebra
    let hσAlg : A →ₐ[K] F :=
      { toRingHom := (algebraMap K F).comp σ
        commutes' := fun c ↦ congrArg (algebraMap K F) (hsec c) }
    let Ψ : TensorProduct K F A →ₐ[K] F :=
      Algebra.TensorProduct.lift (AlgHom.id K F) hσAlg (fun f a ↦ mul_comm _ _)
    ∀ z : TensorProduct K F A, z ≠ 0 →
      ∃ a : A, a ≠ 0 ∧ ∃ z' : TensorProduct K F A,
        z = ((1 : F) ⊗ₜ[K] a) * z' ∧ Ψ z' ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_tensorProduct_exists_primitive_factor.solution

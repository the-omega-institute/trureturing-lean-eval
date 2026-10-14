import Submission.Supplier.Definitions.Def_GaloisRep_Adic
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_GaloisRepAdic_trace_eq_of_trace_frobenius_eq

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
attribute [-instance] FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

set_option autoImplicit false

theorem GaloisRepAdic.trace_eq_of_trace_frobenius_eq
    {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (ρ₁ ρ₂ : GaloisRepAdic A)
    (S : Finset ℕ)
    (hfrob : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∀ (B : ValuationSubring (AlgebraicClosure ℚ))
      (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), B.LiesOverPrime ℓ → B.IsFrobeniusAt τ ℓ →
        ρ₁.trace τ = ρ₂.trace τ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ρ₁.trace σ = ρ₂.trace σ := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_trace_eq_of_trace_frobenius_eq.solution

#print axioms GaloisRepAdic.trace_eq_of_trace_frobenius_eq

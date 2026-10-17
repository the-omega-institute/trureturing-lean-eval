import Mathlib
import Submission.Supplier.Definitions.Def_GroupCohomology_ContinuousUnramified
import Submission.Supplier.Definitions.Def_GroupCohomology_GlobalBridge
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_groupCohomology_exists_isGlobalBridge2

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.exists_isGlobalBridge2
    (S : Finset Nat.Primes)
    {D : Type} [Group D] [Finite D] (π : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* D)
    (hπlev : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
      ∀ s : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), s ∈ F.fixingSubgroup → π s = 1)
    {R P B : Rep ℤ D} (f : R ⟶ P) (g : P ⟶ B)
    (hfg : Function.Exact f.hom g.hom) (hg : Function.Surjective g.hom)
    {X : Rep ℤ D} {A : Rep ℤ (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)} (ι : X →+ A) (hι : Function.Injective ι)
    (hιeq : ∀ (h : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (x : X), ι (X.ρ (π h) x) = A.ρ h (ι x))
    {p : ℕ} {M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)} (κ : B →+ M →+ A)
    (hκeq : ∀ (h : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (b : B) (m : M), κ (B.ρ (π h) b) (M.ρ h m) = A.ρ h (κ b m))
    (hκ : ∀ c : B →+ A, ∃! m : M, ∀ b, κ b m = c b)
    (hdiv : ∀ φ : R →+ X, ∃ ψ : (ihom (Rep.res π P)).obj A,
      (∀ x : R, LinearMap.toAddMonoidHom ψ (f.hom x) = ι (φ x)) ∧
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
        ∀ s : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), s ∈ F.fixingSubgroup → ∀ x : P, A.ρ s (LinearMap.toAddMonoidHom ψ x) = LinearMap.toAddMonoidHom ψ x) :
    ∃ Λ : H1 ((ihom R).obj X) →+ continuousH2S S M, IsGlobalBridge₂ S π f g ι κ Λ := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_isGlobalBridge2.solution

#print axioms groupCohomology.exists_isGlobalBridge2

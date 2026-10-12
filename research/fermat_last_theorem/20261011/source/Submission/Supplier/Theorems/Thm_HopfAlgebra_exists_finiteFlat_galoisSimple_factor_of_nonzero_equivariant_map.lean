import Submission.Supplier.Definitions.Def_GaloisRep_Flat
import Submission.Supplier.Definitions.Def_GaloisRep_TameCharacter
import Submission.Supplier.Definitions.Def_FLTPrelim_Ramification
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_HopfAlgebra_exists_finiteFlat_galoisSimple_factor_of_nonzero_equivariant_map

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
attribute [-simp] closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff

theorem HopfAlgebra.exists_finiteFlat_galoisSimple_factor_of_nonzero_equivariant_map
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {H : Type} [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Flat (GaloisRep.ratLocalizedAt p) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H]
    (hMp : ∀ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ), f ^ p = 1)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (N : Type) [AddCommGroup N] [Module (IsLocalRing.ResidueField P) N]
    (act : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → N →ₗ[IsLocalRing.ResidueField P] N)
    (F : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) → N)
    (hFmul : ∀ f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
      F (f * g) = F f + F g)
    (hFequiv : ∀ σ ∈ P.inertiaSubgroupIn ℚ,
      ∀ f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        (∀ h : H, g h = σ (f h)) → F g = act σ (F f))
    (hFne : ∃ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ), F f ≠ 0) :
    ∃ (H' : Type) (_ : CommRing H') (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) H'),
      Module.Finite (GaloisRep.ratLocalizedAt p) H' ∧
      Module.Flat (GaloisRep.ratLocalizedAt p) H' ∧
      Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H' ∧
      (∀ f : WithConv (H' →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ), f ^ p = 1) ∧
      ∃ F' : WithConv (H' →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) → N,
        (∀ f g : WithConv (H' →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
          F' (f * g) = F' f + F' g) ∧
        (∀ σ ∈ P.inertiaSubgroupIn ℚ,
          ∀ f g : WithConv (H' →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
            (∀ h : H', g h = σ (f h)) → F' g = act σ (F' f)) ∧
        (∃ f : WithConv (H' →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ), F' f ≠ 0) ∧
        (∀ S : Submonoid (WithConv (H' →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
          (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ f ∈ S,
            ∀ g : WithConv (H' →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
              (∀ h : H', g h = σ (f h)) → g ∈ S) →
          S = ⊥ ∨ S = ⊤) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_finiteFlat_galoisSimple_factor_of_nonzero_equivariant_map.solution

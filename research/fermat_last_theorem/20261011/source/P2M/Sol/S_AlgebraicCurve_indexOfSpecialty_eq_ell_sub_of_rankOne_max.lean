import P2M.Sol.S_AlgebraicCurve_exists_genus_riemannIndex_of_stichtenothGenusExists

-- Reuse the checked supplier theorem with the complete original solution declaration.
namespace P2MW.S_AlgebraicCurve_indexOfSpecialty_eq_ell_sub_of_rankOne_max

set_option autoImplicit false

open _root_.P2MW.S_AlgebraicCurve_exists_genus_riemannIndex_of_stichtenothGenusExists.AlgebraicCurve

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F]
    (hRankOne : WeilDifferentialRankOne K F)
    {W : Divisor K F} {φ : Module.Dual K ↥(adeleSpace K F)}
    (hφ : φ ∈ omegaSpace W) (hφ0 : φ ≠ 0)
    (hWmax : ∀ E : Divisor K F, φ ∈ omegaSpace E → E ≤ W) (D : Divisor K F) :
    indexOfSpecialty D = ell (W - D) :=
  _root_.P2MW.S_AlgebraicCurve_exists_genus_riemannIndex_of_stichtenothGenusExists.AlgebraicCurve.indexOfSpecialty_eq_ell_sub_of_rankOne_max (K := K) (F := F) hRankOne hφ hφ0 hWmax D

end P2MW.S_AlgebraicCurve_indexOfSpecialty_eq_ell_sub_of_rankOne_max

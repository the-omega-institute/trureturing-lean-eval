import P2M.Sol.S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists

-- Reuse the checked supplier theorem with the complete original solution declaration.
namespace P2MW.S_AlgebraicCurve_exists_riemannGenusReachedAt_of_bounded

set_option autoImplicit false

open _root_.P2MW.S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.AlgebraicCurve

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F] [FiniteDimensional K ↥(LSpace (0 : Divisor K F))]
    (hbdd : RiemannGenusBounded K F) :
    ∃ (γ : ℤ) (D₀ : Divisor K F), RiemannGenusReachedAt γ D₀ :=
  _root_.P2MW.S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.AlgebraicCurve.exists_riemannGenusReachedAt_of_bounded (K := K) (F := F) hbdd

end P2MW.S_AlgebraicCurve_exists_riemannGenusReachedAt_of_bounded

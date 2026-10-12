import P2M.Sol.S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists

-- Reuse the checked supplier theorem with the complete original solution declaration.
namespace P2MW.S_AlgebraicCurve_ell_sub_ell_le_degree_sub_degree

set_option autoImplicit false

open _root_.P2MW.S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.AlgebraicCurve

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F] {D₁ D₂ : Divisor K F} (hD : D₁ ≤ D₂)
    [FiniteDimensional K ↥(LSpace D₂)] :
    (ell D₂ : ℤ) - (ell D₁ : ℤ) ≤ Divisor.degree D₂ - Divisor.degree D₁ :=
  _root_.P2MW.S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.AlgebraicCurve.ell_sub_ell_le_degree_sub_degree (K := K) (F := F) hD

end P2MW.S_AlgebraicCurve_ell_sub_ell_le_degree_sub_degree

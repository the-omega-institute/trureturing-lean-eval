import P2M.Sol.S_AlgebraicCurve_exists_genus_riemannIndex_of_stichtenothGenusExists

-- Reuse the checked supplier theorem with the complete original solution declaration.
namespace P2MW.S_AlgebraicCurve_weilDifferentialRankOne_of_stichtenothGenusExists

set_option autoImplicit false

open _root_.P2MW.S_AlgebraicCurve_exists_genus_riemannIndex_of_stichtenothGenusExists.AlgebraicCurve

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    (h : StichtenothGenusExists K F) : WeilDifferentialRankOne K F :=
  _root_.P2MW.S_AlgebraicCurve_exists_genus_riemannIndex_of_stichtenothGenusExists.AlgebraicCurve.weilDifferentialRankOne_of_stichtenothGenusExists (K := K) (F := F) h

end P2MW.S_AlgebraicCurve_weilDifferentialRankOne_of_stichtenothGenusExists

import P2M.Sol.S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists

-- Reuse the supplier proof already checked in the imported module.
-- Keep the original solution telescope and conclusion.
namespace P2MW.S_AlgebraicCurve_riemannGenusBounded_of_indexFinite

set_option autoImplicit false

open _root_.P2MW.S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.AlgebraicCurve

theorem solution {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (hfin : IndexOfSpecialtyFinite K F) :
    RiemannGenusBounded K F :=
  _root_.P2MW.S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.AlgebraicCurve.riemannGenusBounded_of_indexFinite (K := K) (F := F) hfin

end P2MW.S_AlgebraicCurve_riemannGenusBounded_of_indexFinite

import P2M.Sol.S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists

-- Reuse the supplier proof already checked in the imported module.
-- Keep the original solution telescope and conclusion.
namespace P2MW.S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists_of_ratFunc_tower

set_option autoImplicit false

open _root_.P2MW.S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.AlgebraicCurve

theorem solution (K : Type*) [Field K] [DecidableEq (RatFunc K)] (F : Type*) [Field F] [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable (RatFunc K) F] [HasPrincipalDivisors K F] [IsCurveOver K F] [Nonempty (Place K F)] [FiniteDimensional K (LSpace (0 : Divisor K F))] :
    StichtenothGenusExists K F :=
  _root_.P2MW.S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.AlgebraicCurve.RationalFunctionField.stichtenothGenusExists_of_ratFunc_tower (K := K) (F := F)

end P2MW.S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists_of_ratFunc_tower

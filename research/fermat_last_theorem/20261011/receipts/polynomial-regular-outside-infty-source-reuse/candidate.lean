import P2M.Sol.S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists

-- Reuse the checked supplier theorem with the complete original solution declaration.
namespace P2MW.S_AlgebraicCurve_RationalFunctionField_algebraMap_polynomial_mem_of_ne_placeInfty

set_option autoImplicit false

open _root_.P2MW.S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.AlgebraicCurve

theorem solution (K : Type*) [Field K] [DecidableEq (RatFunc K)]
    {u : Place K (RatFunc K)} (hu : u ≠ RationalFunctionField.placeInfty K) (q : (Polynomial K)) :
    algebraMap (Polynomial K) (RatFunc K) q ∈ u.toValuationSubring :=
  _root_.P2MW.S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.AlgebraicCurve.RationalFunctionField.algebraMap_polynomial_mem_of_ne_placeInfty K hu q

end P2MW.S_AlgebraicCurve_RationalFunctionField_algebraMap_polynomial_mem_of_ne_placeInfty

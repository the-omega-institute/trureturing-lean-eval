import P2M.Sol.S_AlgebraicCurve_RationalFunctionField_weilReciprocity

namespace P2MW.S_AlgebraicCurve_RationalFunctionField_evalAt_placeInfty_eq

set_option autoImplicit false

open Polynomial _root_.AlgebraicCurve _root_.AlgebraicCurve.RationalFunctionField

theorem solution (K : Type*) [Field K] [DecidableEq (RatFunc K)] {f : RatFunc K} {c : K} (h : f - algebraMap K (RatFunc K) c = 0 ∨ (f - algebraMap K (RatFunc K) c).intDegree < 0) : (placeInfty K).evalAt f = c := by
  exact _root_.P2MW.S_AlgebraicCurve_RationalFunctionField_weilReciprocity.AlgebraicCurve.RationalFunctionField.evalAt_placeInfty_eq (K := K) h

end P2MW.S_AlgebraicCurve_RationalFunctionField_evalAt_placeInfty_eq

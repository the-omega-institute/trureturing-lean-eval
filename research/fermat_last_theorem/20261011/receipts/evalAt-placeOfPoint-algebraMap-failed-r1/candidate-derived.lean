import Submission.Supplier.P2M.Sol.S_AlgebraicCurve_RationalFunctionField_weilReciprocity

namespace P2MW.S_AlgebraicCurve_RationalFunctionField_evalAt_placeOfPoint_algebraMap

set_option autoImplicit false

open _root_.AlgebraicCurve

theorem solution {K : Type*} [Field K] (a : K) (q : Polynomial K) : (placeOfPoint K a).evalAt (algebraMap (Polynomial K) (RatFunc K) q) = q.eval a := by
  exact _root_.P2MW.S_AlgebraicCurve_RationalFunctionField_weilReciprocity.AlgebraicCurve.RationalFunctionField.evalAt_placeOfPoint_algebraMap (K := K) a q

end P2MW.S_AlgebraicCurve_RationalFunctionField_evalAt_placeOfPoint_algebraMap

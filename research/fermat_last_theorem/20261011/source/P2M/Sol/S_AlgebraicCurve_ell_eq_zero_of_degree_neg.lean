import P2M.Sol.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed

namespace P2MW.S_AlgebraicCurve_ell_eq_zero_of_degree_neg

set_option autoImplicit false

open _root_.AlgebraicCurve

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] {D : Divisor K F} [IsCurveOver K F] (hD : Divisor.degree D < 0) :
    ell D = 0 := by
  exact _root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.AlgebraicCurve.ell_eq_zero_of_degree_neg (K := K) (F := F) hD

end P2MW.S_AlgebraicCurve_ell_eq_zero_of_degree_neg

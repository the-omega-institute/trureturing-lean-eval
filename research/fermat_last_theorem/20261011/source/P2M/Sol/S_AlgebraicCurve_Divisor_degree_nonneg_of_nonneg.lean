import Definitions.Def_AlgebraicCurve_IsCurveOver

namespace P2MW.S_AlgebraicCurve_Divisor_degree_nonneg_of_nonneg

set_option autoImplicit false

open _root_.AlgebraicCurve

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    {D : Divisor K F} (hD : ∀ v, 0 ≤ D v) : 0 ≤ Divisor.degree D := by
  change 0 ≤ ∑ v ∈ D.support, D v * (v.deg : ℤ)
  exact Finset.sum_nonneg fun v _ => mul_nonneg (hD v) (Int.natCast_nonneg _)

end P2MW.S_AlgebraicCurve_Divisor_degree_nonneg_of_nonneg

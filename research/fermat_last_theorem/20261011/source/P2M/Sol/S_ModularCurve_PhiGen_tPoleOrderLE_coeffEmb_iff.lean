import P2M.Sol.S_ModularCurve_PhiGen_PhiGenDescends_sum_mul_jqN_pow_eq_zero

namespace P2MW.S_ModularCurve_PhiGen_tPoleOrderLE_coeffEmb_iff

set_option autoImplicit false

noncomputable section

open _root_.ModularCurve _root_.ModularCurve.PhiGen

theorem solution {K : Type*} [Field K] [Algebra ℚ K] (f : LaurentSeries ℚ) (n : ℕ) : TPoleOrderLE (coeffEmb K f) n ↔ TPoleOrderLE f n := by
  exact _root_.P2MW.S_ModularCurve_PhiGen_PhiGenDescends_sum_mul_jqN_pow_eq_zero.ModularCurve.PhiGen.tPoleOrderLE_coeffEmb_iff f n

end

#print axioms solution

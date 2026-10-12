import P2M.Sol.S_ModularCurve_PhiGen_PhiGenDescends_sum_mul_jqN_pow_eq_zero

namespace P2MW.S_ModularCurve_PhiGen_tPoleOrderLE_of_qExpand

set_option autoImplicit false

noncomputable section

open _root_.ModularCurve _root_.ModularCurve.PhiGen

theorem solution {K : Type*} [Field K] {f : LaurentSeries K} {N n : ℕ} [NeZero N]
    (h : TPoleOrderLE (qExpand K N f) (N * n)) : TPoleOrderLE f n := by
  exact _root_.P2MW.S_ModularCurve_PhiGen_PhiGenDescends_sum_mul_jqN_pow_eq_zero.ModularCurve.PhiGen.tPoleOrderLE_of_qExpand h

end

#print axioms solution

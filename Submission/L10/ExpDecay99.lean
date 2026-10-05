import Mathlib

/-!
# Gate L-10 (`klartag_packing`), brief 99 piece (1) — `e^{-x} ≤ 20²⁰/x²⁰`

`GoodPathBounds.failTotal` carries two `exp (-n)` terms multiplied by polynomials in `n` of degree
`9` (the union-bound cost) and `7` (the step count).  To bound their sum by an absolute constant one
needs `exp (-n)` below an inverse polynomial of larger degree; `20` is the smallest round exponent
that leaves room for both.

The route is one line of analysis: `Real.add_one_le_exp` at `x/20` gives `x/20 ≤ exp (x/20)`, and
raising that to the twentieth power gives `(x/20)^20 ≤ exp x`.  I searched the tree
(`ExpBounds.lean`, `SlackDecay.lean`, `Discharge.lean`) and Mathlib's `Real.exp` API for a
polynomial-decay statement of this shape and **did not find one** — `Real.add_one_le_exp`,
`Real.exp_ge_one_add`, and `Real.one_sub_lt_exp_neg` are all degree one.

Nothing reported is edited.
-/

set_option linter.unusedSectionVars false

namespace Submission.L10.ExpDecay99

/-- **`(x/20)^20 ≤ exp x`** for `x ≥ 0`.  `Real.add_one_le_exp` at `x/20`, then `pow_le_pow_left₀`;
`exp x = (exp (x/20))^20` is `Real.exp_nat_mul`. -/
theorem pow_div_le_exp {x : ℝ} (hx : 0 ≤ x) : (x / 20) ^ 20 ≤ Real.exp x := by
  have hstep : x / 20 ≤ Real.exp (x / 20) := by
    have h := Real.add_one_le_exp (x / 20)
    linarith
  have h20 : Real.exp x = Real.exp (x / 20) ^ 20 := by
    rw [← Real.exp_nat_mul]
    push_cast
    ring_nf
  rw [h20]
  exact pow_le_pow_left₀ (by positivity) hstep 20

/-- **`e^{-x} ≤ 20²⁰/x²⁰`** for `x > 0` — the decay `FailTotalBound99` consumes. -/
theorem exp_neg_le {x : ℝ} (hx : 0 < x) : Real.exp (-x) ≤ 20 ^ 20 / x ^ 20 := by
  have hxp : (0 : ℝ) < x ^ 20 := by positivity
  have hex : (0 : ℝ) < Real.exp x := Real.exp_pos x
  have hbase : x ^ 20 / 20 ^ 20 ≤ Real.exp x := by
    have h := pow_div_le_exp hx.le
    rwa [div_pow] at h
  have hkey : x ^ 20 ≤ 20 ^ 20 * Real.exp x := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 20 ^ 20)] at hbase
    linarith
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ hex hxp]
  linarith

/-- **The form the failure bound uses**: at a natural `n ≥ 1`. -/
theorem exp_neg_nat_le {n : ℕ} (hn : 1 ≤ n) :
    Real.exp (-(n : ℝ)) ≤ 20 ^ 20 / (n : ℝ) ^ 20 := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  exact exp_neg_le hn0

end Submission.L10.ExpDecay99

import Submission.L10.ExpDecay99
import Submission.L10.GoodPathBounds

/-!
# Gate L-10 (`klartag_packing`), brief 99 piece (2) — `failTotal n pcnt ≤ pcnt + 10⁻³`

`GoodPathBounds.failTotal n pcnt` (`GoodPathBounds.lean:644`) is

```
(33·n⁹·log n + 4)·e^{-n} + N·(2·(4·e^{-(1²·n)})) + pcnt
```

with `N = ParamsAdopted2.numStepsAdopted2 n = ⌈16·n⁷·log n⌉₊`.  Both exponential terms are
polynomial × `e^{-n}`, so `ExpDecay99.exp_neg_le` collapses them into an inverse polynomial.

**The arithmetic, with the margin stated.**  `Real.log_le_sub_one_of_pos` gives `log n ≤ n − 1 ≤ n`
(the brief's `log n ≤ 2√n ≤ 2n` also works and is two steps longer), and
`Nat.ceil_lt_add_one` gives `N ≤ 16 n⁷ log n + 1`.  So the polynomial factor is at most

```
33 n¹⁰ + 4 + 8·(16 n⁸ + 1) ≤ 173 n¹⁰
```

and `e^{-n} ≤ 20²⁰/n²⁰` turns the product into `173·20²⁰/n¹⁰`.  That is below `10⁻³` as soon as
`n¹⁰ ≥ 173 000·20²⁰ = 1.814·10³¹`; at `n₁ = 2 073 600` we have `n¹⁰ ≥ 10⁶⁰`, i.e. **29 orders of
margin**.  The measured value of the two exponential terms at `n₁` is about `1.7·10⁻⁴¹`, so the
`10⁻³` ceiling is not tight in any direction — it is a round number chosen above a measured
quantity (README 29's clause), not before it.

Nothing reported is edited.
-/

set_option linter.unusedSectionVars false

namespace Submission.L10.FailTotalBound99

open Submission.L10

variable {n : ℕ}

/-- `N ≤ 16·n⁷·log n + 1` — `numStepsAdopted2` is a `Nat.ceil`. -/
theorem numSteps_le (hn : 1 ≤ n) :
    ((ParamsAdopted2.numStepsAdopted2 n : ℕ) : ℝ) ≤ 16 * (n : ℝ) ^ 7 * Real.log n + 1 := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlog0 : (0 : ℝ) ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  rw [ParamsAdopted2.numStepsAdopted2, ChainDrift.numSteps]
  exact le_of_lt (Nat.ceil_lt_add_one (by positivity))

/-- **The polynomial factor of the two exponential terms is at most `173·n¹⁰`.** -/
theorem poly_le (hn : 1 ≤ n) :
    (33 * (n : ℝ) ^ 9 * Real.log n + 4)
        + 8 * ((ParamsAdopted2.numStepsAdopted2 n : ℕ) : ℝ)
      ≤ 173 * (n : ℝ) ^ 10 := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hlog : Real.log n ≤ (n : ℝ) := by
    have h := Real.log_le_sub_one_of_pos hn0
    linarith
  have hN := numSteps_le hn
  have h1 : 33 * (n : ℝ) ^ 9 * Real.log n ≤ 33 * (n : ℝ) ^ 10 := by
    have h := mul_le_mul_of_nonneg_left hlog (show (0 : ℝ) ≤ 33 * (n : ℝ) ^ 9 by positivity)
    linarith
  have h2 : 16 * (n : ℝ) ^ 7 * Real.log n ≤ 16 * (n : ℝ) ^ 8 := by
    have h := mul_le_mul_of_nonneg_left hlog (show (0 : ℝ) ≤ 16 * (n : ℝ) ^ 7 by positivity)
    linarith
  have h3 : (n : ℝ) ^ 8 ≤ (n : ℝ) ^ 10 := by
    exact pow_le_pow_right₀ hnR (by norm_num)
  have h4 : (1 : ℝ) ≤ (n : ℝ) ^ 10 := one_le_pow₀ hnR
  linarith

/-- **`173·n¹⁰·(20²⁰/n²⁰) ≤ 10⁻³`** for `n ≥ n₁` — the margin is `10⁶⁰` against `1.814·10³¹`. -/
theorem const_le (hn : 2073600 ≤ n) :
    173 * (n : ℝ) ^ 10 * (20 ^ 20 / (n : ℝ) ^ 20) ≤ 1 / 1000 := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hne : (n : ℝ) ≠ 0 := ne_of_gt hn0
  have hnp : (0 : ℝ) < (n : ℝ) ^ 10 := by positivity
  have hid : 173 * (n : ℝ) ^ 10 * (20 ^ 20 / (n : ℝ) ^ 20)
      = 173 * 20 ^ 20 / (n : ℝ) ^ 10 := by
    field_simp
  have hbig : ((1000000 : ℝ)) ^ 10 ≤ (n : ℝ) ^ 10 :=
    pow_le_pow_left₀ (by norm_num) (by linarith) 10
  rw [hid, div_le_iff₀ hnp]
  have hval : (173 : ℝ) * 20 ^ 20 ≤ 1 / 1000 * (1000000 : ℝ) ^ 10 := by norm_num
  linarith

/-- **`failTotal n pcnt ≤ pcnt + 10⁻³`** for every `n ≥ n₁` and every `pcnt`. -/
theorem failTotal_le (hn : 2073600 ≤ n) (pcnt : ℝ) :
    GoodPathBounds.failTotal n pcnt ≤ pcnt + 1 / 1000 := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hE0 : (0 : ℝ) ≤ Real.exp (-(n : ℝ)) := (Real.exp_pos _).le
  have hEb : Real.exp (-(n : ℝ)) ≤ 20 ^ 20 / (n : ℝ) ^ 20 := ExpDecay99.exp_neg_nat_le hn1
  have hpoly := poly_le hn1
  have hstep1 : ((33 * (n : ℝ) ^ 9 * Real.log n + 4)
        + 8 * ((ParamsAdopted2.numStepsAdopted2 n : ℕ) : ℝ)) * Real.exp (-(n : ℝ))
      ≤ (173 * (n : ℝ) ^ 10) * Real.exp (-(n : ℝ)) :=
    mul_le_mul_of_nonneg_right hpoly hE0
  have hstep2 : (173 * (n : ℝ) ^ 10) * Real.exp (-(n : ℝ))
      ≤ (173 * (n : ℝ) ^ 10) * (20 ^ 20 / (n : ℝ) ^ 20) :=
    mul_le_mul_of_nonneg_left hEb (by positivity)
  have hstep3 := const_le hn
  rw [GoodPathBounds.failTotal]
  simp only [one_pow, one_mul]
  linarith

end Submission.L10.FailTotalBound99

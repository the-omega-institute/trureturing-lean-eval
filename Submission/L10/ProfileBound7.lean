/-
Gate L-10 (`klartag_packing`), brief 27.

**Lemma 4.3's numeric side conditions.**  Report 26 said "seven"; reading every signature, as this
brief directs, the chain carries **fifteen** distinct non-integrability hypotheses.  They fall into
three groups, and the grouping is the useful part:

* **structural** — positivity and monotonicity of `subst` and `radiusOf`, and `W = radiusOf Y`:
  `hρ`, `hρW`, `hW0`, `hW`, `hlow`.  No parameter values needed.
* **window** — `√t·Y` small enough: `hSc`, `hpos`, `hBs`, `hLs`, `hts`, and shape 4's gap.  One
  inequality implies all six.
* **drift** — `2 ≤ b`, `b/2 ≤ L`, `b ≤ 2A`, `1 ≤ A`, `A ≤ Y` with `b = n√T/2`.  These need the
  parameter values, and at `T = 16·log n/n²` they all reduce to `log n ≥ 1`.

**`n₁ = 3`.**  `b = n√T/2 = 2·√(log n)` exactly, and every drift condition is `log n ≥ 1`, i.e.
`n ≥ 3` (since `e < 3`).  That is the only size threshold Lemma 4.3 imposes, and it is far below
the `n₀` §§3–4 need anyway.
-/
import Submission.L10.ProfileBound6

namespace Submission.L10

open MeasureTheory Set Real
open scoped ENNReal NNReal

/-! ## 1. The drift at the chain's horizon, and `n₁ = 3` -/

/-- `log n ≥ 1` for `n ≥ 3`, because `e < 3`.  **This is `n₁`.** -/
theorem one_le_log_of_three {n : ℕ} (hn : 3 ≤ n) : (1 : ℝ) ≤ Real.log n := by
  have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  rw [Real.le_log_iff_exp_le hn0]
  have : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  linarith

/-- **The drift is `2√(log n)` exactly** at `T = 16·log n/n²`. -/
theorem drift_eq {n : ℕ} (hn : 0 < n) {T : ℝ} (hT : T = 16 * Real.log n / (n : ℝ) ^ 2) :
    (n : ℝ) * Real.sqrt T / 2 = 2 * Real.sqrt (Real.log n) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 hn
  have hsq : Real.sqrt T = 4 * Real.sqrt (Real.log n) / (n : ℝ) := by
    rw [hT, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hn0.le,
      show (16 : ℝ) * Real.log n = 4 ^ 2 * Real.log n by norm_num,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  rw [hsq]
  field_simp
  ring

/-- `√(log n) ≥ 1` for `n ≥ 3`. -/
theorem one_le_sqrt_log {n : ℕ} (hn : 3 ≤ n) : (1 : ℝ) ≤ Real.sqrt (Real.log n) := by
  have h := one_le_log_of_three hn
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_le_sqrt h

/-- `√(log n) ≤ log n` for `n ≥ 3`. -/
theorem sqrt_log_le_log {n : ℕ} (hn : 3 ≤ n) : Real.sqrt (Real.log n) ≤ Real.log n := by
  have h := one_le_log_of_three hn
  have hs := one_le_sqrt_log hn
  have hsq : Real.sqrt (Real.log n) ^ 2 = Real.log n := Real.sq_sqrt (by linarith)
  nlinarith [hs, hsq]

/-! ## 2. The three drift conditions, discharged at `n ≥ 3` -/

/-- `I2_le`'s `hb : 2 ≤ b`. -/
theorem drift_ge_two {n : ℕ} (hn : 3 ≤ n) {T : ℝ} (hT : T = 16 * Real.log n / (n : ℝ) ^ 2) :
    2 ≤ (n : ℝ) * Real.sqrt T / 2 := by
  have hn0 : 0 < n := by omega
  have hlog : (0 : ℝ) ≤ Real.log n := by linarith [one_le_log_of_three hn]
  rw [drift_eq hn0 hT]
  linarith [one_le_sqrt_log hn]

/-- `I2_le`'s `hLb : b/2 ≤ L` at `L = log n`. -/
theorem half_drift_le_log {n : ℕ} (hn : 3 ≤ n) {T : ℝ}
    (hT : T = 16 * Real.log n / (n : ℝ) ^ 2) :
    (n : ℝ) * Real.sqrt T / 2 / 2 ≤ Real.log n := by
  have hn0 : 0 < n := by omega
  have hlog : (0 : ℝ) ≤ Real.log n := by linarith [one_le_log_of_three hn]
  rw [drift_eq hn0 hT]
  linarith [sqrt_log_le_log hn]

/-- `I3_le`'s `hbA : b ≤ 2A` at `A = log n`. -/
theorem drift_le_two_log {n : ℕ} (hn : 3 ≤ n) {T : ℝ}
    (hT : T = 16 * Real.log n / (n : ℝ) ^ 2) :
    (n : ℝ) * Real.sqrt T / 2 ≤ 2 * Real.log n := by
  have hn0 : 0 < n := by omega
  have hlog : (0 : ℝ) ≤ Real.log n := by linarith [one_le_log_of_three hn]
  rw [drift_eq hn0 hT]
  linarith [sqrt_log_le_log hn]

/-- `pieces_sum_le`'s `hA1 : 1 ≤ A` at `A = log n`. -/
theorem one_le_split_point {n : ℕ} (hn : 3 ≤ n) : (1 : ℝ) ≤ Real.log n :=
  one_le_log_of_three hn

/-! ## 3. The window group — one inequality implies six

`√t·Y ≤ 1/2` with `a₀ ≥ 1` gives `hBs`, `hLs`, `hts`, `hpos`, `hSc` and shape 4's gap at
`ε = a₀ − 1/2`. -/

/-- From `√t·Y ≤ 1/2` and `0 ≤ y ≤ Y`: the window's basic inequality. -/
theorem window_mul_le {t Y y : ℝ} (hyY : y ≤ Y)
    (hwin : Y * Real.sqrt t ≤ 1 / 2) : Real.sqrt t * y ≤ 1 / 2 := by
  have hs : (0 : ℝ) ≤ Real.sqrt t := Real.sqrt_nonneg t
  calc Real.sqrt t * y = y * Real.sqrt t := mul_comm _ _
    _ ≤ Y * Real.sqrt t := mul_le_mul_of_nonneg_right hyY hs
    _ ≤ 1 / 2 := hwin

/-- `hpos : 0 < 1 − √t·y` on the window. -/
theorem window_one_sub_pos {t Y y : ℝ} (hyY : y ≤ Y)
    (hwin : Y * Real.sqrt t ≤ 1 / 2) : 0 < 1 - Real.sqrt t * y := by
  have := window_mul_le hyY hwin
  linarith

/-- `hSc : 0 < a₀ − √t·y` on the window, and shape 4's **gap**: `a₀ − 1/2 ≤ a₀ − √t·y`, so the
Jacobian bound of `substDeriv_le` applies with `ε = a₀ − 1/2`. -/
theorem window_gap {a₀ t Y y : ℝ} (hyY : y ≤ Y)
    (hwin : Y * Real.sqrt t ≤ 1 / 2) : a₀ - 1 / 2 ≤ a₀ - Real.sqrt t * y := by
  have := window_mul_le hyY hwin
  linarith

theorem window_sub_pos {a₀ t Y y : ℝ} (ha₀ : 1 ≤ a₀) (hyY : y ≤ Y)
    (hwin : Y * Real.sqrt t ≤ 1 / 2) : 0 < a₀ - Real.sqrt t * y := by
  have := window_gap (a₀ := a₀) hyY hwin
  linarith

/-! ## 4. The structural group — positivity and monotonicity, no parameter values -/

/-- `hρ : 0 ≤ radiusOf 0` — the shell's inner radius is positive. -/
theorem radiusOf_nonneg {a₀ α δ t : ℝ} (hα : 0 < α) (hδ : 0 ≤ δ) (hu : 0 < a₀) :
    0 ≤ radiusOf a₀ α δ t 0 := by
  have hs : 0 < subst a₀ (Real.sqrt t) 0 := by
    refine subst_pos ?_
    simpa using hu
  have : 0 < subst a₀ (Real.sqrt t) 0 / α := div_pos hs hα
  unfold radiusOf
  linarith

/-- `hρW : radiusOf 0 ≤ radiusOf Y` and `hW : radiusOf y ≤ radiusOf Y` — monotonicity. -/
theorem radiusOf_le_end {a₀ α δ t Y y : ℝ} (hα : 0 < α) (ht : 0 < t) (hY : 0 ≤ Y)
    (hy0 : 0 ≤ y) (hyY : y ≤ Y)
    (hS : ∀ z ∈ Icc (0 : ℝ) Y, 0 < a₀ - Real.sqrt t * z) :
    radiusOf a₀ α δ t y ≤ radiusOf a₀ α δ t Y :=
  (strictMonoOn_radiusOf hα ht hS).monotoneOn ⟨hy0, hyY⟩ ⟨hY, le_rfl⟩ hyY

end Submission.L10

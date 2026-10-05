/-
Gate L-10 (`klartag_packing`), brief 30.

**`hJ` as a theorem.**  Report 28 left the junk hypothesis's endpoint value as a *recorded number*
rather than a Lean proof — the one such place in Lemma 4.3.  This closes it.

**The trade.**  The true threshold is `n ≥ 839` (report 27, by bisection on the closed form).  The
*cheaply provable* threshold is `n ≥ 1440² = 2,073,600`, a factor of 2,472 larger, and it buys a
proof with no numeric search in it:

  `log n ≥ 1` ⟹ `(log n)^{3/2} ≤ (log n)³`;  `n + 2 ≤ 2n`;  so the endpoint is `≤ 20(log n)³/n`;
  `Real.log_le_rpow_div` at `ε = 1/6` gives `log n ≤ 6·n^{1/6}`, hence `(log n)³ ≤ 216·√n`;
  so the endpoint is `≤ 4320/√n ≤ 3` exactly when `√n ≥ 1440`.

The trade costs nothing: the gate's `n₀` is set by §§3–4's "n sufficiently large" and by Cor. 3.2,
both far stronger, and the statement is universally quantified so no small `n` is ever evaluated.
-/
import Submission.L10.ProfileBound8

namespace Submission.L10

open Real

/-! ## 1. `log n ≤ 6·n^{1/6}`, and its cube -/

/-- `Real.log_le_rpow_div` at `ε = 1/6`. -/
theorem log_le_six_rpow {n : ℕ} : Real.log n ≤ 6 * (n : ℝ) ^ ((1 : ℝ) / 6) := by
  have h := Real.log_le_rpow_div (x := (n : ℝ)) (Nat.cast_nonneg n) (by norm_num : (0:ℝ) < 1/6)
  calc Real.log n ≤ (n : ℝ) ^ ((1 : ℝ) / 6) / (1 / 6) := h
    _ = 6 * (n : ℝ) ^ ((1 : ℝ) / 6) := by ring

/-- `(log n)³ ≤ 216·√n`.  Cubing `log n ≤ 6·n^{1/6}` and `(n^{1/6})³ = n^{1/2} = √n`. -/
theorem log_cube_le {n : ℕ} (hn : 1 ≤ n) : (Real.log n) ^ 3 ≤ 216 * Real.sqrt n := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog0 : (0 : ℝ) ≤ Real.log n := Real.log_nonneg hn1
  have hrp0 : (0 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 6) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hcube : ((n : ℝ) ^ ((1 : ℝ) / 6)) ^ 3 = Real.sqrt n := by
    rw [← Real.rpow_natCast ((n : ℝ) ^ ((1 : ℝ) / 6)) 3, ← Real.rpow_mul (Nat.cast_nonneg n),
      Real.sqrt_eq_rpow]
    norm_num
  calc (Real.log n) ^ 3 ≤ (6 * (n : ℝ) ^ ((1 : ℝ) / 6)) ^ 3 :=
        pow_le_pow_left₀ hlog0 log_le_six_rpow 3
    _ = 216 * ((n : ℝ) ^ ((1 : ℝ) / 6)) ^ 3 := by ring
    _ = 216 * Real.sqrt n := by rw [hcube]

/-! ## 2. The crude reduction to `20·(log n)³/n` -/

/-- With `√t ≤ 4√(log n)/n` and `y ≤ log n`, the endpoint value is at most `20·(log n)³/n`. -/
theorem endpoint_le_crude {n : ℕ} (hn : 3 ≤ n) {t : ℝ}
    (hts : Real.sqrt t ≤ 4 * Real.sqrt (Real.log n) / (n : ℝ)) :
    Real.log n * Real.sqrt t + ((n : ℝ) + 2) / 2 * (Real.log n * Real.sqrt t) ^ 2
      ≤ 20 * (Real.log n) ^ 3 / (n : ℝ) := by
  have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log n := one_le_log_of_three hn
  have hL0 : (0 : ℝ) ≤ Real.log n := by linarith
  have hsl : Real.sqrt (Real.log n) ^ 2 = Real.log n := Real.sq_sqrt hL0
  have hsl0 : (0 : ℝ) ≤ Real.sqrt (Real.log n) := Real.sqrt_nonneg _
  have hs0 : (0 : ℝ) ≤ Real.sqrt t := Real.sqrt_nonneg t
  -- the linear term
  have hlin : Real.log n * Real.sqrt t ≤ 4 * Real.log n * Real.sqrt (Real.log n) / (n : ℝ) := by
    calc Real.log n * Real.sqrt t
        ≤ Real.log n * (4 * Real.sqrt (Real.log n) / (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hts hL0
      _ = 4 * Real.log n * Real.sqrt (Real.log n) / (n : ℝ) := by ring
  have hlin0 : (0 : ℝ) ≤ Real.log n * Real.sqrt t := mul_nonneg hL0 hs0
  -- `log n · √(log n) ≤ (log n)^2`, since `√(log n) ≤ log n`
  have hsqle : Real.sqrt (Real.log n) ≤ Real.log n := sqrt_log_le_log hn
  have hlin2 : Real.log n * Real.sqrt t ≤ 4 * (Real.log n) ^ 2 / (n : ℝ) := by
    refine le_trans hlin ?_
    rw [div_le_div_iff_of_pos_right hn0]
    nlinarith [hsqle, hL0, hL1]
  -- the quadratic term
  have hquad : ((n : ℝ) + 2) / 2 * (Real.log n * Real.sqrt t) ^ 2
      ≤ 16 * (Real.log n) ^ 3 / (n : ℝ) := by
    have hsq : (Real.log n * Real.sqrt t) ^ 2 ≤ 16 * (Real.log n) ^ 3 / (n : ℝ) ^ 2 := by
      have h1 : (Real.log n * Real.sqrt t) ^ 2
          ≤ (4 * Real.log n * Real.sqrt (Real.log n) / (n : ℝ)) ^ 2 :=
        pow_le_pow_left₀ hlin0 hlin 2
      refine le_trans h1 (le_of_eq ?_)
      field_simp
      nlinarith [hsl]
    have hn2 : ((n : ℝ) + 2) / 2 ≤ (n : ℝ) := by linarith
    have hsq0 : (0 : ℝ) ≤ 16 * (Real.log n) ^ 3 / (n : ℝ) ^ 2 := by positivity
    calc ((n : ℝ) + 2) / 2 * (Real.log n * Real.sqrt t) ^ 2
        ≤ ((n : ℝ) + 2) / 2 * (16 * (Real.log n) ^ 3 / (n : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hsq (by linarith)
      _ ≤ (n : ℝ) * (16 * (Real.log n) ^ 3 / (n : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right hn2 hsq0
      _ = 16 * (Real.log n) ^ 3 / (n : ℝ) := by field_simp
  -- `4(log n)² ≤ 4(log n)³` since `log n ≥ 1`
  have hcub : 4 * (Real.log n) ^ 2 / (n : ℝ) ≤ 4 * (Real.log n) ^ 3 / (n : ℝ) := by
    rw [div_le_div_iff_of_pos_right hn0]
    nlinarith [hL1, hL0]
  have : 4 * (Real.log n) ^ 3 / (n : ℝ) + 16 * (Real.log n) ^ 3 / (n : ℝ)
      = 20 * (Real.log n) ^ 3 / (n : ℝ) := by ring
  linarith [hlin2, hquad, hcub, this.ge, this.le]

/-! ## 3. `hJ` at `J = 3`, for `n ≥ 1440² = 2,073,600` -/

/-- **`hJ`, proved.**  The endpoint value of the junk term is at most `3` for every
`n ≥ 2,073,600`.  No number stands in for a proof. -/
theorem junk_endpoint_le_three {n : ℕ} (hn : 2073600 ≤ n) {t : ℝ}
    (hts : Real.sqrt t ≤ 4 * Real.sqrt (Real.log n) / (n : ℝ)) :
    Real.log n * Real.sqrt t + ((n : ℝ) + 2) / 2 * (Real.log n * Real.sqrt t) ^ 2 ≤ 3 := by
  have hn3 : 3 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  refine le_trans (endpoint_le_crude hn3 hts) ?_
  -- `20(log n)³/n ≤ 20·216·√n/n = 4320/√n ≤ 3`
  have hcube := log_cube_le hn1
  have hsn : (1440 : ℝ) ≤ Real.sqrt n := by
    rw [show (1440 : ℝ) = Real.sqrt (1440 ^ 2) by
      rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num; linarith)
  have hsn0 : (0 : ℝ) < Real.sqrt n := by linarith
  have hsq : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt hn0.le
  rw [div_le_iff₀ hn0]
  nlinarith [hcube, hsn, hsn0, hsq]

end Submission.L10

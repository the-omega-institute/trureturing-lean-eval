/-
Gate L-10 (`klartag_packing`), brief 92.

**The one pure-constant input report 90 left open.**

`TerminalRatio.thetaTight_terminal_le` (`:74`) carries the hypothesis

  `hKcR : Real.exp (1 / 2) * Lemma43R.KcR ≤ 826`

and nothing in the tree proves it, because nothing bounds `exp 3` or `exp 6` from above.  This
module closes it from `Real.exp_one_lt_d9` and `Real.pi_gt_d2` alone (`Real.pi_gt_314` does not exist at
this pin; the `3.14 < π` lemma is `Real.pi_gt_d2`, `Mathlib/Analysis/Real/Pi/Bounds.lean:159`).

**The chain, with every margin checked exactly (rational arithmetic, `norm_num`):**

| step | bound | true value | slack |
|---|---|---|---|
| `exp 3 ≤ 20.0856` | `2.7182818286³ = 20.085536926…` | `20.085536923…` | `6.3·10⁻⁵` |
| `exp 6 ≤ 403.429` | `2.7182818286⁶ = 403.428793618…` | `403.428793493…` | `2.1·10⁻⁴` |
| `exp (1/2) ≤ 1.64873` | `1.64873² = 2.7183106 > 2.7182818286` | `1.648721271…` | `8.7·10⁻⁶` |
| `√(2π) ≥ 2.505` | `2.505² = 6.275025 ≤ 6.28 < 2π` | `2.506628…` | `1.6·10⁻³` |
| `2/√(2π) ≤ 0.799` | `0.799·2.505 = 2.001495 ≥ 2` | `0.797885…` | `1.1·10⁻³` |
| `KcR ≤ 500.83` | `403.429 + 20.0856·2.799 + 40.1712 + 1 = 500.8197944` | `500.796 9` | `0.033` |
| **`e^{1/2}·KcR ≤ 826`** | `1.64873 · 500.83 = 825.733 4` | **`825.674 5`** | **`0.267`** |

**`exp 6` must not be routed through `exp 3`.**  `20.0856² = 403.431 3 > 403.429`, so squaring the
`exp 3` bound overshoots the target.  `exp_one_pow_six` goes to `(exp 1)^6` directly.

**Kill rule 2.**  Nothing here is dimension-dependent; every statement is a closed numeric
inequality.
-/
import Submission.L10.TerminalRatio

namespace Submission.L10.ExpBounds

open Real Submission.L10

/-! ## 1. Powers of `e` -/

theorem exp_one_pow_three : Real.exp 3 = Real.exp 1 ^ 3 := by
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have h3 : Real.exp 3 = Real.exp 1 * Real.exp 2 := by rw [← Real.exp_add]; norm_num
  rw [h3, h2]; ring

theorem exp_one_pow_six : Real.exp 6 = Real.exp 1 ^ 6 := by
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have h4 : Real.exp 4 = Real.exp 2 * Real.exp 2 := by rw [← Real.exp_add]; norm_num
  have h6 : Real.exp 6 = Real.exp 2 * Real.exp 4 := by rw [← Real.exp_add]; norm_num
  rw [h6, h4, h2]; ring

/-- `e³ ≤ 20.0856`. -/
theorem exp_three_le : Real.exp 3 ≤ 20.0856 := by
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hpow : Real.exp 1 ^ 3 ≤ (2.7182818286 : ℝ) ^ 3 :=
    pow_le_pow_left₀ h0.le he.le 3
  have hnum : (2.7182818286 : ℝ) ^ 3 ≤ 20.0856 := by norm_num
  rw [exp_one_pow_three]
  linarith

/-- `e⁶ ≤ 403.429`.  Note this is **not** `(e³)²`: `20.0856² = 403.4313` overshoots. -/
theorem exp_six_le : Real.exp 6 ≤ 403.429 := by
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hpow : Real.exp 1 ^ 6 ≤ (2.7182818286 : ℝ) ^ 6 :=
    pow_le_pow_left₀ h0.le he.le 6
  have hnum : (2.7182818286 : ℝ) ^ 6 ≤ 403.429 := by norm_num
  rw [exp_one_pow_six]
  linarith

/-- `e^{1/2} ≤ 1.64873`, from `(e^{1/2})² = e < 2.7182818286 < 1.64873²`. -/
theorem exp_half_le : Real.exp (1 / 2) ≤ 1.64873 := by
  have hsq : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h0 : (0 : ℝ) < Real.exp (1 / 2) := Real.exp_pos _
  by_cases h : Real.exp (1 / 2) ≤ 1.64873
  · exact h
  · exfalso
    have hcon : (1.64873 : ℝ) < Real.exp (1 / 2) := not_le.mp h
    nlinarith [hsq, he, hcon, h0]

/-! ## 2. `√(2π)` from below -/

theorem sqrt_two_pi_ge : (2.505 : ℝ) ≤ Real.sqrt (2 * π) := by
  have hpi : (3.14 : ℝ) < π := Real.pi_gt_d2
  rw [show (2.505 : ℝ) = Real.sqrt (2.505 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt (by nlinarith [hpi])

theorem two_div_sqrt_two_pi_le : 2 / Real.sqrt (2 * π) ≤ 0.799 := by
  have h := sqrt_two_pi_ge
  have h0 : (0 : ℝ) < Real.sqrt (2 * π) := by linarith
  rw [div_le_iff₀ h0]
  nlinarith [h]

/-! ## 3. `KcR`, and the binder `TerminalRatio` leaves open -/

theorem KcR_le : Lemma43R.KcR ≤ 500.83 := by
  have h3 := exp_three_le
  have h6 := exp_six_le
  have hd := two_div_sqrt_two_pi_le
  have h3pos : (0 : ℝ) < Real.exp 3 := Real.exp_pos 3
  have hb : 2 / Real.sqrt (2 * π) + 2 ≤ 2.799 := by linarith
  have hbpos : (0 : ℝ) ≤ 2 / Real.sqrt (2 * π) + 2 := by positivity
  have hprod : Real.exp 3 * (2 / Real.sqrt (2 * π) + 2) ≤ 20.0856 * 2.799 :=
    mul_le_mul h3 hb hbpos (by norm_num)
  rw [Lemma43R.KcR, Kc]
  linarith

/-- **The hypothesis `TerminalRatio.thetaTight_terminal_le` takes**, discharged.  Verbatim its
`hKcR` binder (`TerminalRatio.lean:78`). -/
theorem exp_half_mul_KcR_le : Real.exp (1 / 2) * Lemma43R.KcR ≤ 826 := by
  have hh := exp_half_le
  have hk := KcR_le
  have hk0 : 0 ≤ Lemma43R.KcR := Lemma43R.KcR_nonneg
  calc Real.exp (1 / 2) * Lemma43R.KcR
      ≤ 1.64873 * 500.83 := mul_le_mul hh hk hk0 (by norm_num)
    _ ≤ 826 := by norm_num

end Submission.L10.ExpBounds

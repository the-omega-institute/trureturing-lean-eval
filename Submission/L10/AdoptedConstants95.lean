/-
Gate L-10 (`klartag_packing`), brief 95 item (4)(a) — the three arithmetic facts about the adopted
constants that `TruncSumMean.hLb_of_bounds` carries as hypotheses.

* `mAt_le_one` → `kappa_ge_half`: `κ = (1/2 + 2rr)/mAt²` is at least `1/2` because `mAt ≤ 1`.
  The content is `a0C n − 1 ≤ r0Adopted n`: the left side is `(2n−1)/(n−1)² ≤ 4/n`, the right is
  `24√(log n/n) ≥ 4/n`, with a factor of about `6·10⁴` to spare at `n₁`.
* `logDet_A0C_le`: `logDet (A0C n) = n·log(a0C n) ≤ 2n/(n−1) ≤ 3`, from
  `Real.log_le_sub_one_of_pos` applied to `1/(1−1/n)`.
* `log_ratio_le`: `200·log n/n ≤ 100`, via `log n ≤ 2√n`.

Each is extracted as its own lemma rather than pushed through one tactic call (README 19).
Nothing reported is edited.
-/
import Submission.L10.TruncSumMean

set_option linter.unusedSectionVars false

namespace Submission.L10.AdoptedConstants95

open Finset Module Submission.L10 Submission.L10.Increments
open Submission.L10.RawDataInst2 Submission.L10.Tiling

variable {n : ℕ}

/-! ## 1. `a0C n − 1 ≤ 4/n` -/

theorem a0C_sub_one_le (hn : 3 ≤ n) : a0C n - 1 ≤ 4 / (n : ℝ) := by
  have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hu : (0 : ℝ) < 1 - 1 / (n : ℝ) := by
    rw [sub_pos, div_lt_one hn0]; linarith
  have hune : (1 : ℝ) - 1 / (n : ℝ) ≠ 0 := ne_of_gt hu
  rw [a0C, ← sub_nonneg]
  have hkey : 4 / (n : ℝ) - ((1 - 1 / (n : ℝ))⁻¹ ^ 2 - 1)
      = (2 * (n : ℝ) ^ 2 - 7 * (n : ℝ) + 4) / ((n : ℝ) * ((n : ℝ) - 1) ^ 2) := by
    have hn1 : (n : ℝ) - 1 ≠ 0 := by intro h; nlinarith
    field_simp
    ring
  rw [hkey]
  have hnum : (0 : ℝ) ≤ 2 * (n : ℝ) ^ 2 - 7 * (n : ℝ) + 4 := by nlinarith [hn3]
  have hden : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) ^ 2 := by
    have : (0 : ℝ) < ((n : ℝ) - 1) ^ 2 := by nlinarith [hn3]
    positivity
  positivity

/-! ## 2. `4/n ≤ r0Adopted n` -/

theorem four_div_le_r0 (hn : 3 ≤ n) : 4 / (n : ℝ) ≤ DriftStopped6.r0Adopted n := by
  have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hlog : (1 : ℝ) ≤ Real.log n := ChainDrift.log_pos_of_three hn
  have hq : (0 : ℝ) ≤ Real.log n / (n : ℝ) := by positivity
  have hsqrt : 1 / (6 * (n : ℝ)) ≤ Real.sqrt (Real.log n / (n : ℝ)) := by
    have hsq : (1 / (6 * (n : ℝ))) ^ 2 ≤ Real.log n / (n : ℝ) := by
      rw [div_pow, one_pow, div_le_div_iff₀ (by positivity) hn0]
      have : (1 : ℝ) * (n : ℝ) ≤ Real.log n * (6 * (n : ℝ)) ^ 2 := by nlinarith [hlog, hn3]
      linarith
    have h0 : (0 : ℝ) ≤ 1 / (6 * (n : ℝ)) := by positivity
    calc 1 / (6 * (n : ℝ)) = Real.sqrt ((1 / (6 * (n : ℝ))) ^ 2) := (Real.sqrt_sq h0).symm
      _ ≤ Real.sqrt (Real.log n / (n : ℝ)) := Real.sqrt_le_sqrt hsq
  rw [DriftStopped6.r0Adopted]
  have : 4 / (n : ℝ) = 24 * (1 / (6 * (n : ℝ))) := by field_simp; ring
  rw [this]
  linarith [hsqrt]

/-! ## 3. `mAt ≤ 1`, hence `κ ≥ 1/2` -/

theorem mAt_le_one (hn : 3 ≤ n) {c₃ : ℝ} (hc₃ : 0 ≤ c₃) :
    GoodPathBounds.mAt n c₃ ≤ 1 := by
  have h1 := a0C_sub_one_le (n := n) hn
  have h2 := four_div_le_r0 (n := n) hn
  have h3 : (0 : ℝ) ≤ c₃ * DriftStopped6.etaAdopted n :=
    mul_nonneg hc₃ (DriftStopped7.etaAdopted_nonneg (n := n))
  rw [GoodPathBounds.mAt]
  linarith

/-- **`κ ≥ 1/2`**, `hLb_of_bounds`'s first hypothesis. -/
theorem kappa_ge_half (hn : 2073600 ≤ n) {c₃ rr : ℝ} (hc₃ : 0 ≤ c₃)
    (hc₃η : c₃ * DriftStopped6.etaAdopted n ≤ 1 / 4) (hrr : 0 ≤ rr) :
    1 / 2 ≤ (1 / 2 + 2 * rr) / GoodPathBounds.mAt n c₃ ^ 2 := by
  have hhalf := GoodPathBounds.half_le_mAt hn hc₃η
  have hm0 : (0 : ℝ) < GoodPathBounds.mAt n c₃ := by linarith
  have hle := mAt_le_one (n := n) (by omega) hc₃
  have hsq : GoodPathBounds.mAt n c₃ ^ 2 ≤ 1 := by nlinarith [hm0, hle]
  have hsq0 : (0 : ℝ) < GoodPathBounds.mAt n c₃ ^ 2 := by positivity
  rw [le_div_iff₀ hsq0]
  nlinarith [hsq, hrr, hsq0]

/-! ## 4. `logDet (A0C n) ≤ 3` -/

theorem logDet_A0C_eq (hn : 3 ≤ n) :
    ChainWiring.logDet (A0C n) = (n : ℝ) * Real.log (a0C n) := by
  have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have ha0 : (0 : ℝ) < a0C n := by
    have := DriftStopped7.one_le_a0C (n := n) (by omega); linarith
  rw [ChainWiring.logDet, StateSupply.symMat_A0C n, Matrix.det_smul, Matrix.det_one, mul_one,
    Real.log_pow]
  simp [Fintype.card_fin]

theorem logDet_A0C_le (hn : 3 ≤ n) : ChainWiring.logDet (A0C n) ≤ 3 := by
  have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hu : (0 : ℝ) < 1 - 1 / (n : ℝ) := by
    rw [sub_pos, div_lt_one hn0]; linarith
  -- `log (a0C n) = -2 log (1 - 1/n) ≤ 2/(n-1)`
  have hlogu : -Real.log (1 - 1 / (n : ℝ)) ≤ 1 / ((n : ℝ) - 1) := by
    have h := Real.log_le_sub_one_of_pos (x := (1 - 1 / (n : ℝ))⁻¹) (by positivity)
    rw [Real.log_inv] at h
    have hid : (1 - 1 / (n : ℝ))⁻¹ - 1 = 1 / ((n : ℝ) - 1) := by
      have hn1 : (n : ℝ) - 1 ≠ 0 := by intro hz; nlinarith
      field_simp
      ring
    linarith [h, hid.le, hid.ge]
  have ha0log : Real.log (a0C n) ≤ 2 / ((n : ℝ) - 1) := by
    rw [a0C, Real.log_pow, Real.log_inv]
    have : ((2 : ℕ) : ℝ) = 2 := by norm_num
    rw [this]
    have h2 : (2 : ℝ) / ((n : ℝ) - 1) = 2 * (1 / ((n : ℝ) - 1)) := by ring
    rw [h2]
    linarith [hlogu]
  have hmul : (n : ℝ) * Real.log (a0C n) ≤ (n : ℝ) * (2 / ((n : ℝ) - 1)) :=
    mul_le_mul_of_nonneg_left ha0log (by linarith)
  have hfin : (n : ℝ) * (2 / ((n : ℝ) - 1)) ≤ 3 := by
    rw [mul_div_assoc'] at *
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < (n : ℝ) - 1)]
    nlinarith [hn3]
  rw [logDet_A0C_eq hn]
  linarith

/-! ## 5. `200·log n/n ≤ 100` -/

theorem log_ratio_le (hn : 2073600 ≤ n) : 200 * Real.log n / (n : ℝ) ≤ 100 := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hs : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hn0.le
  have hs0 : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
  have hsge : (1440 : ℝ) ≤ Real.sqrt (n : ℝ) := by nlinarith [hs, hs0, hnR]
  -- `log n = 2 log √n ≤ 2(√n − 1) ≤ 2√n`
  have hlog : Real.log n ≤ 2 * Real.sqrt (n : ℝ) := by
    have hh := Real.log_le_sub_one_of_pos hs0
    have hsplit : Real.log (Real.sqrt (n : ℝ)) = Real.log n / 2 :=
      Real.log_sqrt hn0.le
    rw [hsplit] at hh
    linarith [hh, hs0]
  rw [div_le_iff₀ hn0]
  nlinarith [hlog, hs, hs0, hsge]

end Submission.L10.AdoptedConstants95

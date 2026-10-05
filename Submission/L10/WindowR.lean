/-
Gate L-10 (`klartag_packing`), brief 70 part A.

**The reach window.**

Report 68: `Profile.profile` is `0` beyond the window, `supp ⊆ window`, and the state's lower
eigenvalue bound `DriftStopped6.mAdopted = a₀ − (r₀ + c₃η) = 0.936438` is **below** `winNum⁻² =
0.999894`, so the final ellipsoid reaches lattice points the old window does not cover.  This
module moves the window out to the reach, tying it to `DriftStopped6.mAdopted` itself rather than
to a hand-chosen constant, so a later change to `r₀` or `c₃η` moves the window with it.

`YR n·√T = a0C n − mR n` **identically in `t`**, so `window_small` becomes `mR n ≥ a0C n − 1/2` —
proved here with room to spare (`r₀ + c₃η ≤ 1/2` at `n ≥ 2 073 600`).
-/
import Submission.L10.DriftStopped6
import Submission.L10.GaussianMaximal3

namespace Submission.L10.WindowR

open MeasureTheory Set Real Submission.L10 Submission.L10.Increments
open scoped ENNReal NNReal

/-! ## 1. The adopted lower eigenvalue bound -/

/-- The adopted lower bound on the state's quadratic form, `DriftStopped6.mAdopted`. -/
noncomputable def mR (n : ℕ) : ℝ := DriftStopped6.mAdopted n

theorem mR_eq (n : ℕ) :
    mR n = a0C n - (DriftStopped6.r0Adopted n + DriftStopped6.c3Adopted n
      * DriftStopped6.etaAdopted n) := rfl

/-- `log n ≤ 4·n^{1/4}`, from `log x ≤ x − 1` at `x = n^{1/4}`. -/
theorem log_le_four_qrt {n : ℕ} (hn : 2073600 ≤ n) :
    Real.log n ≤ 4 * Real.sqrt (Real.sqrt (n : ℝ)) := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hsn : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
  have hs : (0 : ℝ) < Real.sqrt (Real.sqrt (n : ℝ)) := Real.sqrt_pos.2 hsn
  have hlog : Real.log (Real.sqrt (Real.sqrt (n : ℝ))) = Real.log n / 4 := by
    rw [Real.log_sqrt hsn.le, Real.log_sqrt hn0.le]; ring
  have hle := Real.log_le_sub_one_of_pos hs
  rw [hlog] at hle
  linarith

/-- `√√n ≥ 37` at the threshold (`√√2 073 600 = 37.947`). -/
theorem qrt_ge {n : ℕ} (hn : 2073600 ≤ n) : (37 : ℝ) ≤ Real.sqrt (Real.sqrt (n : ℝ)) := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1 : (1440 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    rw [show (1440 : ℝ) = Real.sqrt (1440 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num; linarith)
  rw [show (37 : ℝ) = Real.sqrt (37 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt (by norm_num; linarith)

theorem qrt_pow_four {n : ℕ} (hn : 0 ≤ (n : ℝ)) :
    Real.sqrt (Real.sqrt (n : ℝ)) ^ 4 = (n : ℝ) := by
  have h1 : Real.sqrt (Real.sqrt (n : ℝ)) ^ 2 = Real.sqrt (n : ℝ) :=
    Real.sq_sqrt (Real.sqrt_nonneg _)
  calc Real.sqrt (Real.sqrt (n : ℝ)) ^ 4
      = (Real.sqrt (Real.sqrt (n : ℝ)) ^ 2) ^ 2 := by ring
    _ = Real.sqrt (n : ℝ) ^ 2 := by rw [h1]
    _ = (n : ℝ) := Real.sq_sqrt hn

theorem r0Adopted_nonneg (n : ℕ) : 0 ≤ DriftStopped6.r0Adopted n := by
  rw [DriftStopped6.r0Adopted]; positivity

theorem r0Adopted_sq {n : ℕ} (hn : 1 ≤ n) :
    DriftStopped6.r0Adopted n ^ 2 = 576 * (Real.log n / (n : ℝ)) := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hL : (0 : ℝ) ≤ Real.log n := Real.log_nonneg hnR
  rw [DriftStopped6.r0Adopted, mul_pow, Real.sq_sqrt (by positivity)]
  norm_num

/-- `9216·log n ≤ n` at the threshold. -/
theorem log_mul_le {n : ℕ} (hn : 2073600 ≤ n) : 9216 * Real.log n ≤ (n : ℝ) := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hs37 : (37 : ℝ) ≤ Real.sqrt (Real.sqrt (n : ℝ)) := qrt_ge hn
  have hs0 : (0 : ℝ) < Real.sqrt (Real.sqrt (n : ℝ)) := by linarith
  have hs4 : Real.sqrt (Real.sqrt (n : ℝ)) ^ 4 = (n : ℝ) := qrt_pow_four hn0.le
  have hLs : Real.log n ≤ 4 * Real.sqrt (Real.sqrt (n : ℝ)) := log_le_four_qrt hn
  have hcube : (37 : ℝ) ^ 3 ≤ Real.sqrt (Real.sqrt (n : ℝ)) ^ 3 :=
    pow_le_pow_left₀ (by norm_num) hs37 3
  nlinarith [hLs, hcube, hs0, hs4]

theorem r0Adopted_le {n : ℕ} (hn : 2073600 ≤ n) : DriftStopped6.r0Adopted n ≤ 1 / 4 := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hsq : DriftStopped6.r0Adopted n ^ 2 = 576 * (Real.log n / (n : ℝ)) :=
    r0Adopted_sq (by omega)
  have hfin : 576 * (Real.log n / (n : ℝ)) ≤ 1 / 16 := by
    rw [show (576 : ℝ) * (Real.log n / (n : ℝ)) = 576 * Real.log n / (n : ℝ) by ring,
      div_le_iff₀ hn0]
    linarith [log_mul_le hn]
  have h16 : DriftStopped6.r0Adopted n ^ 2 ≤ 1 / 16 := by rw [hsq]; exact hfin
  nlinarith [r0Adopted_nonneg n, h16]

theorem c3eta_le {n : ℕ} (hn : 2073600 ≤ n) :
    DriftStopped6.c3Adopted n * DriftStopped6.etaAdopted n ≤ 1 / 4 := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hη : DriftStopped6.etaAdopted n ≤ Real.sqrt 2 / (n : ℝ) ^ 3 :=
    ParamsAdopted2.eta2_le (by omega)
  have hs2 : Real.sqrt 2 ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt (2 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have h3 : (0 : ℝ) < (n : ℝ) ^ 3 := by positivity
  rw [DriftStopped6.c3Adopted]
  have hmul : (n : ℝ) ^ 2 * DriftStopped6.etaAdopted n
      ≤ (n : ℝ) ^ 2 * (Real.sqrt 2 / (n : ℝ) ^ 3) :=
    mul_le_mul_of_nonneg_left hη (by positivity)
  have hval : (n : ℝ) ^ 2 * (Real.sqrt 2 / (n : ℝ) ^ 3) = Real.sqrt 2 / (n : ℝ) := by
    field_simp
  rw [hval] at hmul
  have : Real.sqrt 2 / (n : ℝ) ≤ 2 / 2073600 := by
    rw [div_le_div_iff₀ hn0 (by norm_num)]
    nlinarith
  linarith

/-- **`window_small` at the reach**: `mR n ≥ a0C n − 1/2`. -/
theorem mR_ge {n : ℕ} (hn : 2073600 ≤ n) : a0C n - 1 / 2 ≤ mR n := by
  rw [mR_eq]
  linarith [r0Adopted_le hn, c3eta_le hn]

theorem mR_pos {n : ℕ} (hn : 2073600 ≤ n) : 0 < mR n := by
  have h1 : (1 : ℝ) ≤ a0C n := a0C_ge_one (by omega)
  linarith [mR_ge hn]

theorem mR_lt_one {n : ℕ} (hn : 2073600 ≤ n) : mR n < 1 := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hL : (6 : ℝ) ≤ Real.log n := six_le_log hn
  -- `a0C n ≤ 1 + 3/n`
  have hinv : (0 : ℝ) < 1 - 1 / (n : ℝ) := by
    have : 1 / (n : ℝ) ≤ 1 / 2073600 := by
      rw [div_le_div_iff₀ hn0 (by norm_num)]; linarith
    linarith
  have ha0 : a0C n ≤ 1 + 3 / (n : ℝ) := by
    rw [a0C, inv_pow, ← one_div, div_le_iff₀ (by positivity)]
    field_simp
    nlinarith [hn0, hnR]
  -- `3/n ≤ r₀`
  have hr0 : 3 / (n : ℝ) ≤ DriftStopped6.r0Adopted n := by
    have hsq := r0Adopted_sq (n := n) (by omega)
    have hgoal : (3 / (n : ℝ)) ^ 2 ≤ DriftStopped6.r0Adopted n ^ 2 := by
      rw [hsq, div_pow, div_le_iff₀ (by positivity)]
      have hrw : (576 : ℝ) * (Real.log n / (n : ℝ)) * (n : ℝ) ^ 2
          = 576 * Real.log n * (n : ℝ) := by field_simp
      rw [hrw]
      nlinarith [hL, hn0]
    nlinarith [r0Adopted_nonneg n, hgoal, hn0]
  have hηpos : 0 < DriftStopped6.c3Adopted n * DriftStopped6.etaAdopted n := by
    have hd : (0 : ℝ) < (Fintype.card (UT n) : ℝ) := by
      exact_mod_cast card_UT_pos (by omega)
    have hh : 0 < ParamsAdopted2.stepSizeAdopted2 n := stepSizeAdopted2_pos (by omega)
    rw [DriftStopped6.c3Adopted, DriftStopped6.etaAdopted]
    have : (0 : ℝ) < 2 * ParamsAdopted2.stepSizeAdopted2 n
        * (Fintype.card (UT n) : ℝ) * (n : ℝ) := by positivity
    have := Real.sqrt_pos.2 this
    positivity
  rw [mR_eq]
  linarith

/-! ## 2. The reach window -/

/-- The `y`-endpoint of the reach window: `YR n·√T = a0C n − mR n`, identically in `t`. -/
noncomputable def YR (n : ℕ) : ℝ := (a0C n - mR n) / Real.sqrt (ChainDrift.horizon n)

/-- The reach window's numerator: `windowR α n = reachNum n/α + √n/2` by `rfl`. -/
noncomputable def reachNum (n : ℕ) : ℝ :=
  subst (a0C n) (Real.sqrt (ChainDrift.horizon n)) (YR n)

/-- **The reach window.** -/
noncomputable def windowR (α : ℝ) (n : ℕ) : ℝ :=
  radiusOf (a0C n) α (Real.sqrt n / 2) (ChainDrift.horizon n) (YR n)

theorem windowR_eq (α : ℝ) (n : ℕ) : windowR α n = reachNum n / α + Real.sqrt n / 2 := rfl

theorem sqrtT_pos {n : ℕ} (hn : 3 ≤ n) : 0 < Real.sqrt (ChainDrift.horizon n) :=
  Real.sqrt_pos.2 (horizon_pos hn)

/-- `√T·YR = a0C − mR`, the identity that makes `window_small` `t`-free. -/
theorem sqrtT_mul_YR {n : ℕ} (hn : 3 ≤ n) :
    Real.sqrt (ChainDrift.horizon n) * YR n = a0C n - mR n := by
  rw [YR, mul_div_cancel₀ _ (ne_of_gt (sqrtT_pos hn))]

/-- **`reachNum = 1/√(mR)`.** -/
theorem reachNum_eq {n : ℕ} (hn : 2073600 ≤ n) : reachNum n = 1 / Real.sqrt (mR n) := by
  have h := sqrtT_mul_YR (n := n) (by omega)
  rw [reachNum, subst, h]
  have : a0C n - (a0C n - mR n) = mR n := by ring
  rw [this, one_div]

theorem one_lt_reachNum {n : ℕ} (hn : 2073600 ≤ n) : 1 < reachNum n := by
  rw [reachNum_eq hn]
  have hm : 0 < mR n := mR_pos hn
  have hlt : mR n < 1 := mR_lt_one hn
  have hs : Real.sqrt (mR n) < 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_lt_sqrt hm.le hlt
  have hs0 : 0 < Real.sqrt (mR n) := Real.sqrt_pos.2 hm
  rw [lt_div_iff₀ hs0]; linarith

/-- **The old window is inside the new one.** -/
theorem windowC_le_windowR {α : ℝ} {n : ℕ} (hα : 0 < α) (hn : 2073600 ≤ n) :
    windowC α n ≤ windowR α n := by
  have hn3 : 3 ≤ n := by omega
  have hT : 0 < Real.sqrt (ChainDrift.horizon n) := sqrtT_pos hn3
  have hwin : Real.log n * Real.sqrt (ChainDrift.horizon n) ≤ 1 / 2 :=
    logn_sqrtT_le hn (horizon_eq n)
  have ha1 : (1 : ℝ) ≤ a0C n := a0C_ge_one (by omega)
  have hL6 : (6 : ℝ) ≤ Real.log n := six_le_log hn
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hle : Real.log n ≤ YR n := by
    rw [YR, le_div_iff₀ hT]
    have hsum : a0C n - mR n = DriftStopped6.r0Adopted n
        + DriftStopped6.c3Adopted n * DriftStopped6.etaAdopted n := by rw [mR_eq]; ring
    rw [hsum]
    have hηnn : 0 ≤ DriftStopped6.c3Adopted n * DriftStopped6.etaAdopted n := by
      rw [DriftStopped6.c3Adopted, DriftStopped6.etaAdopted]; positivity
    have hs37 : (37 : ℝ) ≤ Real.sqrt (Real.sqrt (n : ℝ)) := qrt_ge hn
    have hs0 : (0 : ℝ) < Real.sqrt (Real.sqrt (n : ℝ)) := by linarith
    have hs4 : Real.sqrt (Real.sqrt (n : ℝ)) ^ 4 = (n : ℝ) := qrt_pow_four hn0.le
    have hLs : Real.log n ≤ 4 * Real.sqrt (Real.sqrt (n : ℝ)) := log_le_four_qrt hn
    have hsq1 : (Real.log n * Real.sqrt (ChainDrift.horizon n)) ^ 2
        = Real.log n ^ 2 * ChainDrift.horizon n := by
      rw [mul_pow, Real.sq_sqrt (horizon_pos hn3).le]
    have hsq2 : DriftStopped6.r0Adopted n ^ 2 = 576 * (Real.log n / (n : ℝ)) :=
      r0Adopted_sq (by omega)
    have hcmp : (Real.log n * Real.sqrt (ChainDrift.horizon n)) ^ 2
        ≤ DriftStopped6.r0Adopted n ^ 2 := by
      rw [hsq1, hsq2, horizon_eq]
      rw [show Real.log n ^ 2 * (16 * Real.log n / (n : ℝ) ^ 2)
          = 16 * Real.log n ^ 3 / (n : ℝ) ^ 2 by ring,
        show (576 : ℝ) * (Real.log n / (n : ℝ)) = 576 * Real.log n / (n : ℝ) by ring,
        div_le_div_iff₀ (by positivity) hn0]
      have hL2 : Real.log n ^ 2 ≤ 16 * Real.sqrt (Real.sqrt (n : ℝ)) ^ 2 := by
        nlinarith [hLs, hL6, hs0]
      have hkey : 16 * Real.log n ^ 2 ≤ 576 * (n : ℝ) := by
        nlinarith [hL2, hs4, hs37, hs0]
      have hmul := mul_le_mul_of_nonneg_right hkey
        (mul_nonneg (by linarith : (0 : ℝ) ≤ Real.log n) hn0.le)
      nlinarith [hmul]
    have hpos1 : 0 ≤ Real.log n * Real.sqrt (ChainDrift.horizon n) := by
      have := Real.sqrt_nonneg (ChainDrift.horizon n); nlinarith
    nlinarith [hcmp, hpos1, r0Adopted_nonneg n, hηnn]
  have hSc : ∀ z ∈ Icc (0 : ℝ) (YR n), 0 < a0C n - Real.sqrt (ChainDrift.horizon n) * z := by
    intro z hz
    have : Real.sqrt (ChainDrift.horizon n) * z
        ≤ Real.sqrt (ChainDrift.horizon n) * YR n := by
      exact mul_le_mul_of_nonneg_left hz.2 hT.le
    rw [sqrtT_mul_YR hn3] at this
    linarith [mR_pos hn]
  have hY0 : (0 : ℝ) ≤ YR n := le_trans (by linarith) hle
  exact radiusOf_le_end hα (horizon_pos hn3) hY0 (by linarith) hle hSc

/-- **`window_lt_p` at the reach**: `2·reachNum n ≤ α·p` and `α·√n ≤ 1` give `windowR α n < p`. -/
theorem windowR_lt_p {α p : ℝ} {n : ℕ} (hn : 2073600 ≤ n) (hα : 0 < α)
    (h2 : 2 * reachNum n ≤ α * p) (hsn : α * Real.sqrt n ≤ 1) : windowR α n < p := by
  have h1 : (1 : ℝ) < reachNum n := one_lt_reachNum hn
  have hαp : (1 : ℝ) < α * p := by linarith
  have hrn : reachNum n / α ≤ p / 2 := by
    rw [div_le_iff₀ hα]; nlinarith
  have hsq : Real.sqrt n / 2 ≤ 1 / (2 * α) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  have hhalf : 1 / (2 * α) < p / 2 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  rw [windowR_eq]
  linarith

end Submission.L10.WindowR

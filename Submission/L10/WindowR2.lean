/-
Gate L-10 (`klartag_packing`), brief 85a part A.

**A generous, `c₃`-free window.**

`WindowR.mR := DriftStopped6.mAdopted` ties the window to the *adopted* contact threshold
`c3Adopted n = n²`.  Report 82a shows that threshold fails its own budget, so `c₃` must rise, and
with it the reach.  Rather than re-tie the window to each new `c₃`, this module bases it on the
**weakest** eigenvalue bound the far band can use at all:

`mR2 n := a0C n − 1/2`,

which is exactly the hypothesis `WindowR.mR_ge` supplies (`window_small`), now true by `le_refl`.
`GoodPathBounds.mAt n c₃ = a0C n − (r₀ + c₃η) ≥ mR2 n` for **every** `c₃` with `c₃η ≤ 1/4`
(`mAt_ge_mR2`), since `r₀ ≤ 1/4` at `n ≥ 2 073 600`.  So the band closes at `windowR2` for every
admissible contact threshold and no later change of `c₃` moves this window again.

The price is the reach: `reachNum2 = 1/√(a0C − 1/2) ≈ √2 = 1.41421` against `WindowR.reachNum`'s
`1.03338`.  `windowR ≤ windowR2` and `windowC ≤ windowR2` are proved below, so every containment
already established at the smaller windows survives.
-/
import Submission.L10.WindowR
import Submission.L10.GoodPathBounds

namespace Submission.L10.WindowR2

open MeasureTheory Set Real Submission.L10 Submission.L10.Increments
open scoped ENNReal NNReal

/-! ## 1. The generic lower eigenvalue bound -/

/-- The weakest eigenvalue bound the far band can use: `a0C n − 1/2`. -/
noncomputable def mR2 (n : ℕ) : ℝ := a0C n - 1 / 2

/-- **`window_small` at the generic reach**, now `le_refl`. -/
theorem mR2_ge (n : ℕ) : a0C n - 1 / 2 ≤ mR2 n := le_refl _

/-- `a0C n ≤ 1 + 3/n`. -/
theorem a0C_le_one_add {n : ℕ} (hn : 2073600 ≤ n) : a0C n ≤ 1 + 3 / (n : ℝ) := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hinv : (0 : ℝ) < 1 - 1 / (n : ℝ) := by
    have : 1 / (n : ℝ) ≤ 1 / 2073600 := by
      rw [div_le_div_iff₀ hn0 (by norm_num)]; linarith
    linarith
  rw [a0C, inv_pow, ← one_div, div_le_iff₀ (by positivity)]
  field_simp
  nlinarith [hn0, hnR]

theorem mR2_pos {n : ℕ} (hn : 2073600 ≤ n) : 0 < mR2 n := by
  have h1 : (1 : ℝ) ≤ a0C n := a0C_ge_one (by omega)
  rw [mR2]; linarith

theorem half_le_mR2 {n : ℕ} (hn : 2073600 ≤ n) : (1 : ℝ) / 2 ≤ mR2 n := by
  have h1 : (1 : ℝ) ≤ a0C n := a0C_ge_one (by omega)
  rw [mR2]; linarith

theorem mR2_lt_one {n : ℕ} (hn : 2073600 ≤ n) : mR2 n < 1 := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have h3 : 3 / (n : ℝ) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ hn0 (by norm_num)]; linarith
  have h := a0C_le_one_add hn
  rw [mR2]; linarith

/-- `mR2` is below the adopted `mAdopted`, so `YR ≤ YR2`. -/
theorem mR2_le_mR {n : ℕ} (hn : 2073600 ≤ n) : mR2 n ≤ WindowR.mR n := by
  rw [mR2, WindowR.mR_eq]
  linarith [WindowR.r0Adopted_le hn, WindowR.c3eta_le hn]

/-- **The band closes at `windowR2` for every admissible contact threshold.**  This is the point
of the module: `c₃` may change without the window moving. -/
theorem mAt_ge_mR2 {n : ℕ} (hn : 2073600 ≤ n) {c₃ : ℝ} (_hc₃0 : 0 ≤ c₃)
    (hc₃ : c₃ * DriftStopped6.etaAdopted n ≤ 1 / 4) :
    mR2 n ≤ GoodPathBounds.mAt n c₃ := by
  rw [mR2, GoodPathBounds.mAt]
  linarith [WindowR.r0Adopted_le hn]

/-! ## 2. The generic reach window -/

/-- `YR2 n·√T = a0C n − mR2 n = 1/2`, identically in `t`. -/
noncomputable def YR2 (n : ℕ) : ℝ := (a0C n - mR2 n) / Real.sqrt (ChainDrift.horizon n)

/-- The generic reach window's numerator: `windowR2 α n = reachNum2 n/α + √n/2` by `rfl`. -/
noncomputable def reachNum2 (n : ℕ) : ℝ :=
  subst (a0C n) (Real.sqrt (ChainDrift.horizon n)) (YR2 n)

/-- **The generic reach window.** -/
noncomputable def windowR2 (α : ℝ) (n : ℕ) : ℝ :=
  radiusOf (a0C n) α (Real.sqrt n / 2) (ChainDrift.horizon n) (YR2 n)

theorem windowR2_eq (α : ℝ) (n : ℕ) : windowR2 α n = reachNum2 n / α + Real.sqrt n / 2 := rfl

theorem sqrtT_mul_YR2 {n : ℕ} (hn : 3 ≤ n) :
    Real.sqrt (ChainDrift.horizon n) * YR2 n = a0C n - mR2 n := by
  rw [YR2, mul_div_cancel₀ _ (ne_of_gt (WindowR.sqrtT_pos hn))]

/-- **`reachNum2 = 1/√(mR2)`.** -/
theorem reachNum2_eq {n : ℕ} (hn : 2073600 ≤ n) : reachNum2 n = 1 / Real.sqrt (mR2 n) := by
  have h := sqrtT_mul_YR2 (n := n) (by omega)
  rw [reachNum2, subst, h]
  have : a0C n - (a0C n - mR2 n) = mR2 n := by ring
  rw [this, one_div]

theorem one_lt_reachNum2 {n : ℕ} (hn : 2073600 ≤ n) : 1 < reachNum2 n := by
  rw [reachNum2_eq hn]
  have hm : 0 < mR2 n := mR2_pos hn
  have hlt : mR2 n < 1 := mR2_lt_one hn
  have hs : Real.sqrt (mR2 n) < 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_lt_sqrt hm.le hlt
  have hs0 : 0 < Real.sqrt (mR2 n) := Real.sqrt_pos.2 hm
  rw [lt_div_iff₀ hs0]; linarith

/-- `reachNum2 ≤ 3/2` — the numerical head-room `window_lt_p` needs (`≈ √2 = 1.41421`). -/
theorem reachNum2_le {n : ℕ} (hn : 2073600 ≤ n) : reachNum2 n ≤ 3 / 2 := by
  have hm : (1 : ℝ) / 2 ≤ mR2 n := half_le_mR2 hn
  have h07 : ((7 : ℝ) / 10) ≤ Real.sqrt (mR2 n) := by
    rw [show ((7 : ℝ) / 10) = Real.sqrt ((7 / 10) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith [hm])
  rw [reachNum2_eq hn, div_le_iff₀ (by linarith)]
  linarith

/-! ## 3. The two containments -/

theorem YR_le_YR2 {n : ℕ} (hn : 2073600 ≤ n) : WindowR.YR n ≤ YR2 n := by
  have hT : 0 < Real.sqrt (ChainDrift.horizon n) := WindowR.sqrtT_pos (by omega)
  have h := mR2_le_mR hn
  rw [WindowR.YR, YR2]
  gcongr

theorem YR_nonneg {n : ℕ} (hn : 2073600 ≤ n) : (0 : ℝ) ≤ WindowR.YR n := by
  have hT : 0 < Real.sqrt (ChainDrift.horizon n) := WindowR.sqrtT_pos (by omega)
  have h1 : (1 : ℝ) ≤ a0C n := a0C_ge_one (by omega)
  have h2 : WindowR.mR n < 1 := WindowR.mR_lt_one hn
  rw [WindowR.YR]
  exact div_nonneg (by linarith) hT.le

/-- **The adopted reach window is inside the generic one.** -/
theorem windowR_le_windowR2 {α : ℝ} {n : ℕ} (hα : 0 < α) (hn : 2073600 ≤ n) :
    WindowR.windowR α n ≤ windowR2 α n := by
  have hn3 : 3 ≤ n := by omega
  have hT : 0 < Real.sqrt (ChainDrift.horizon n) := WindowR.sqrtT_pos hn3
  have hYle : WindowR.YR n ≤ YR2 n := YR_le_YR2 hn
  have hY0 : (0 : ℝ) ≤ WindowR.YR n := YR_nonneg hn
  have hY20 : (0 : ℝ) ≤ YR2 n := le_trans hY0 hYle
  have hSc : ∀ z ∈ Icc (0 : ℝ) (YR2 n), 0 < a0C n - Real.sqrt (ChainDrift.horizon n) * z := by
    intro z hz
    have h1 : Real.sqrt (ChainDrift.horizon n) * z
        ≤ Real.sqrt (ChainDrift.horizon n) * YR2 n :=
      mul_le_mul_of_nonneg_left hz.2 hT.le
    rw [sqrtT_mul_YR2 hn3] at h1
    linarith [mR2_pos hn]
  exact radiusOf_le_end hα (horizon_pos hn3) hY20 hY0 hYle hSc

/-- **The old window is inside the generic one.** -/
theorem windowC_le_windowR2 {α : ℝ} {n : ℕ} (hα : 0 < α) (hn : 2073600 ≤ n) :
    windowC α n ≤ windowR2 α n :=
  le_trans (WindowR.windowC_le_windowR hα hn) (windowR_le_windowR2 hα hn)

/-- **`window_lt_p` at the generic reach**: `2·reachNum2 n ≤ α·p` and `α·√n ≤ 1` give
`windowR2 α n < p`.  `reachNum2 ≈ √2`, so the hypothesis is `2.829 ≤ α·p`. -/
theorem windowR2_lt_p {α p : ℝ} {n : ℕ} (hn : 2073600 ≤ n) (hα : 0 < α)
    (h2 : 2 * reachNum2 n ≤ α * p) (hsn : α * Real.sqrt n ≤ 1) : windowR2 α n < p := by
  have h1 : (1 : ℝ) < reachNum2 n := one_lt_reachNum2 hn
  have hαp : (1 : ℝ) < α * p := by linarith
  have hrn : reachNum2 n / α ≤ p / 2 := by
    rw [div_le_iff₀ hα]; nlinarith
  have hsq : Real.sqrt n / 2 ≤ 1 / (2 * α) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  have hhalf : 1 / (2 * α) < p / 2 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  rw [windowR2_eq]
  linarith

end Submission.L10.WindowR2

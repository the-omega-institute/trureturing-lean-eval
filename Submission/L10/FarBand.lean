/-
Gate L-10 (`klartag_packing`), brief 70 part B.

**The fourth piece: the far band.**

Report 68 §3.  Beyond the old window the three-piece split cannot go — `HJ.junk_endpoint_le_three`
caps the `y`-endpoint at `231` while the reach needs `8640` — so the band is handled by a direct
Gaussian estimate.

**The split point is `2·log n`, not `log n`.**  At `log n` the two terms `b·Y₀ = 2·L^{3/2}` and
`a·Y₀² ≈ L²/2` nearly cancel (`5.17` at `n₁`), leaving no room for a bound uniform in `n`.  At
`2·log n` they do not: `b·Y₀ − a·Y₀² ≤ 4·L^{3/2} − 2·L² ≤ 0` for `L ≥ 4`, so the exponential factor
is at most `1`.  The junk bound still holds at `2·log n` (`0.048` against `3` at `n₁`), so the near
piece simply runs there instead.

The estimate is elementary: on `y ≥ Y₀` the quadratic `b·y − a·y²` sits below the **linear**
`(b·Y₀ − a·Y₀²) − (2a·Y₀ − b)(y − Y₀)`, the gap being `a·(y − Y₀)²`, so the tail integral is an
exponential one — `exp_neg_integrableOn_Ioi` and `integral_exp_neg_Ioi` suffice and no rescaled
Gaussian integral is needed.
-/
import Submission.L10.WindowR

namespace Submission.L10.FarBand

open MeasureTheory Set Real Submission.L10
open scoped ENNReal NNReal

/-! ## 1. The quadratic is below a line -/

theorem quad_le_lin {a b Y₀ y : ℝ} (ha : 0 ≤ a) (_hy : Y₀ ≤ y) :
    b * y - a * y ^ 2 ≤ (b * Y₀ - a * Y₀ ^ 2) - (2 * a * Y₀ - b) * (y - Y₀) := by
  nlinarith [sq_nonneg (y - Y₀), ha]

/-! ## 2. The linear exponential integral -/

theorem integrableOn_exp_shift {lam Y₀ C : ℝ} (hlam : 0 < lam) :
    IntegrableOn (fun y : ℝ => Real.exp (C - lam * (y - Y₀))) (Ioi Y₀) := by
  have hbase : IntegrableOn (fun y : ℝ => Real.exp (-lam * y)) (Ioi Y₀) :=
    exp_neg_integrableOn_Ioi Y₀ hlam
  have hfun : (fun y : ℝ => Real.exp (C - lam * (y - Y₀)))
      = fun y : ℝ => Real.exp (C + lam * Y₀) * Real.exp (-lam * y) := by
    funext y; rw [← Real.exp_add]; congr 1; ring
  rw [hfun]
  exact hbase.const_mul _

theorem integral_exp_shift {lam Y₀ C : ℝ} (hlam : 0 < lam) :
    ∫ y in Ioi Y₀, Real.exp (C - lam * (y - Y₀)) = Real.exp C / lam := by
  have hbase : ∫ y in Ioi Y₀, Real.exp (-lam * y) = Real.exp (-lam * Y₀) / lam := by
    have h := integral_comp_mul_left_Ioi (fun x : ℝ => Real.exp (-x)) Y₀ hlam
    simp only [smul_eq_mul] at h
    have hfun : (fun y : ℝ => Real.exp (-lam * y))
        = fun y : ℝ => (fun x : ℝ => Real.exp (-x)) (lam * y) := by
      funext y; congr 1; ring
    rw [hfun, h, integral_exp_neg_Ioi, show -(lam * Y₀) = -lam * Y₀ by ring, div_eq_inv_mul]
  have hfun : (fun y : ℝ => Real.exp (C - lam * (y - Y₀)))
      = fun y : ℝ => Real.exp (C + lam * Y₀) * Real.exp (-lam * y) := by
    funext y; rw [← Real.exp_add]; congr 1; ring
  rw [hfun, MeasureTheory.integral_const_mul, hbase,
    show Real.exp (C + lam * Y₀) * (Real.exp (-lam * Y₀) / lam)
      = Real.exp (C + lam * Y₀) * Real.exp (-lam * Y₀) / lam by ring, ← Real.exp_add,
    show C + lam * Y₀ + -lam * Y₀ = C by ring]

/-! ## 3. The integrand bound -/

/-- `Φ(y)·(1 − y·s)^{−c} ≤ e^{b·y − a·y²}/(√(2π)·Y₀)` on `y ≥ Y₀ > 0` with `y·s ≤ 1/2`,
`b = c·s`, `a = 1/2 − c·s²`. -/
theorem integrand_le {s c Y₀ y : ℝ} (hs : 0 ≤ s) (hc : 0 ≤ c) (hY₀ : 0 < Y₀) (hyY : Y₀ ≤ y)
    (hys : y * s ≤ 1 / 2) :
    Phi y * (1 - y * s) ^ (-c)
      ≤ Real.exp (c * s * y - (1 / 2 - c * s ^ 2) * y ^ 2) / (Real.sqrt (2 * π) * Y₀) := by
  have hpi : (0 : ℝ) < Real.sqrt (2 * π) := Real.sqrt_pos.2 (by positivity)
  have hy0 : 0 < y := lt_of_lt_of_le hY₀ hyY
  have hys0 : 0 ≤ y * s := mul_nonneg hy0.le hs
  have h1 : (0 : ℝ) < 1 - y * s := by linarith
  have hPhi : Phi y ≤ Real.exp (-y ^ 2 / 2) / (Real.sqrt (2 * π) * Y₀) := by
    refine le_trans (min_le_right _ _) ?_
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity)
      (mul_le_mul_of_nonneg_left hyY hpi.le)
  have hrpow : (1 - y * s) ^ (-c) ≤ Real.exp (c * (y * s + (y * s) ^ 2)) := by
    rw [Real.rpow_def_of_pos h1]
    refine Real.exp_le_exp.2 ?_
    have hlog := neg_log_one_sub_le hys0 hys
    nlinarith [hlog, hc]
  have hPhi0 : 0 ≤ Phi y := Phi_nonneg hy0
  have hrp0 : (0 : ℝ) < (1 - y * s) ^ (-c) := Real.rpow_pos_of_pos h1 _
  calc Phi y * (1 - y * s) ^ (-c)
      ≤ (Real.exp (-y ^ 2 / 2) / (Real.sqrt (2 * π) * Y₀))
          * Real.exp (c * (y * s + (y * s) ^ 2)) :=
        mul_le_mul hPhi hrpow hrp0.le (by positivity)
    _ = Real.exp (c * s * y - (1 / 2 - c * s ^ 2) * y ^ 2) / (Real.sqrt (2 * π) * Y₀) := by
        rw [div_mul_eq_mul_div, ← Real.exp_add]
        congr 2
        ring

/-! ## 4. The far band -/

/-- **The far-band bound.**  `Y₀` is the split point, `Y₁` the reach endpoint. -/
theorem far_le {s c Y₀ Y₁ p : ℝ} (hs : 0 ≤ s) (hc : 0 ≤ c) (hY₀ : 0 < Y₀) (hp : 0 ≤ p)
    (hY₁ : Y₁ * s ≤ 1 / 2)
    (hlam : 0 < 2 * (1 / 2 - c * s ^ 2) * Y₀ - c * s)
    (hint : IntegrableOn (fun y : ℝ => Phi y * (1 - y * s) ^ (-c)) (Ioc Y₀ Y₁)) :
    p * ∫ y in Ioc Y₀ Y₁, Phi y * (1 - y * s) ^ (-c)
      ≤ p * (Real.exp (c * s * Y₀ - (1 / 2 - c * s ^ 2) * Y₀ ^ 2)
          / ((2 * (1 / 2 - c * s ^ 2) * Y₀ - c * s) * (Real.sqrt (2 * π) * Y₀))) := by
  set a : ℝ := 1 / 2 - c * s ^ 2 with hadef
  set b : ℝ := c * s with hbdef
  set lam : ℝ := 2 * a * Y₀ - b with hlamdef
  set C₀ : ℝ := b * Y₀ - a * Y₀ ^ 2 with hC₀
  have hpi : (0 : ℝ) < Real.sqrt (2 * π) := Real.sqrt_pos.2 (by positivity)
  have ha : 0 ≤ a := by nlinarith [hlam, hY₀, hs, hc, mul_nonneg hc (sq_nonneg s)]
  have hmaj : IntegrableOn
      (fun y : ℝ => Real.exp (C₀ - lam * (y - Y₀)) / (Real.sqrt (2 * π) * Y₀)) (Ioi Y₀) :=
    (integrableOn_exp_shift hlam).div_const _
  have hstep1 : ∫ y in Ioc Y₀ Y₁, Phi y * (1 - y * s) ^ (-c)
      ≤ ∫ y in Ioc Y₀ Y₁, Real.exp (C₀ - lam * (y - Y₀)) / (Real.sqrt (2 * π) * Y₀) := by
    refine setIntegral_mono_on hint (hmaj.mono_set Ioc_subset_Ioi_self) measurableSet_Ioc ?_
    intro y hy
    have hys : y * s ≤ 1 / 2 := le_trans (mul_le_mul_of_nonneg_right hy.2 hs) hY₁
    refine le_trans (integrand_le hs hc hY₀ hy.1.le hys) ?_
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    exact Real.exp_le_exp.2 (quad_le_lin ha hy.1.le)
  have hstep2 : ∫ y in Ioc Y₀ Y₁, Real.exp (C₀ - lam * (y - Y₀)) / (Real.sqrt (2 * π) * Y₀)
      ≤ ∫ y in Ioi Y₀, Real.exp (C₀ - lam * (y - Y₀)) / (Real.sqrt (2 * π) * Y₀) := by
    refine setIntegral_mono_set hmaj ?_ (Filter.Eventually.of_forall (fun y hy => Ioc_subset_Ioi_self hy))
    filter_upwards with y using by positivity
  have hval : ∫ y in Ioi Y₀, Real.exp (C₀ - lam * (y - Y₀)) / (Real.sqrt (2 * π) * Y₀)
      = Real.exp C₀ / (lam * (Real.sqrt (2 * π) * Y₀)) := by
    rw [MeasureTheory.integral_div, integral_exp_shift hlam]
    field_simp
  refine mul_le_mul_of_nonneg_left ?_ hp
  rw [← hval]
  exact le_trans hstep1 hstep2

end Submission.L10.FarBand

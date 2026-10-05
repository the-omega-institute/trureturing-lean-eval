/-
Gate L-10 (`klartag_packing`), brief 35.

**Lemma 4.3 uniformly in `t ∈ (0,T]`.**  `ProfileBound8.hgbound_chained` pins the window by
`hWdef : W = radiusOf a₀ α (√n/2) t Y`, so it applies at one time only.  Two moves make it
uniform, at the cost of a single factor `e²` in the constant:

* **the reparameterisation.**  Hold `W` fixed and move the `y`-endpoint instead:
  `Y_t := yOf a₀ t (α·(W − √n/2))` inverts `radiusOf`, so `hWdef` holds at every `t`.  The
  identity `Y_t·√t = √T·Y` is exact and `t`-free, so `window_small` and both junk conditions
  transfer verbatim from `t = T`.
* **the small-`t` branch.**  `pieces_at_params` needs `2 ≤ n√t/2`, i.e. `t ≥ t₀ := 16/n²`.
  Below `t₀` the profile's monotonicity in `t` reduces the bound to the one at `t₀`, where
  `e^{n²t₀/8} = e²`.

`Y` is not free: `HJ.junk_endpoint_le_three` is proved at the endpoint `log n`, so the chain's
window is `W = radiusOf a₀ α (√n/2) T (log n)`.
-/
import Submission.L10.Lemma43Final
import Submission.L10.ProfileBound8

namespace Submission.L10

open MeasureTheory Set Real Submission.L10.ChainDataInst Submission.L10.Tiling
open Submission.L10.Section5 Submission.L10.ConstructionA
open scoped ENNReal NNReal

/-! ## 1. `profile` is monotone in `t`, and `radiusOf` inverts `yOf` -/

/-- `t ↦ PhiC (yOf a₀ t u)` is monotone: `yOf` is `c/√t`, which decreases in `t` when `c ≥ 0`
(and `PhiC` is antitone), while for `c < 0` both values are negative and `PhiC` is `1/2` at both. -/
theorem PhiC_yOf_mono {a₀ u t t' : ℝ} (ht : 0 < t) (htt : t ≤ t') :
    PhiC (yOf a₀ t u) ≤ PhiC (yOf a₀ t' u) := by
  have hs : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.2 ht
  have hs' : Real.sqrt t ≤ Real.sqrt t' := Real.sqrt_le_sqrt htt
  have hs'0 : (0 : ℝ) < Real.sqrt t' := lt_of_lt_of_le hs hs'
  by_cases h : 0 ≤ a₀ - (u ^ 2)⁻¹
  · refine PhiC_antitone ?_
    unfold yOf
    gcongr
  · have h' : a₀ - (u ^ 2)⁻¹ < 0 := not_le.1 h
    rw [PhiC_of_nonpos (le_of_lt (by unfold yOf; exact div_neg_of_neg_of_pos h' hs)),
      PhiC_of_nonpos (le_of_lt (by unfold yOf; exact div_neg_of_neg_of_pos h' hs'0))]

/-- **The profile is monotone in `t`.**  This is what the small-`t` branch runs on. -/
theorem profile_mono_time {a₀ α W : ℝ} {n : ℕ} {t t' : ℝ} (ht : 0 < t) (htt : t ≤ t') (r : ℝ) :
    profile a₀ α W n t r ≤ profile a₀ α W n t' r := by
  unfold profile
  split_ifs
  · exact le_rfl
  · exact le_rfl
  · exact PhiC_yOf_mono ht htt

/-- `radiusOf` at `y = 0` is `t`-free: this is why Lemma 4.3's inner-ball term is a constant. -/
theorem radiusOf_zero_eq {a₀ α δ t : ℝ} : radiusOf a₀ α δ t 0 = (Real.sqrt a₀)⁻¹ / α + δ := by
  unfold radiusOf subst; norm_num

/-- **`radiusOf` inverts `yOf`.**  This is the reparameterisation. -/
theorem radiusOf_yOf {a₀ α δ v t : ℝ} (ht : 0 < t) (hv : 0 < v) :
    radiusOf a₀ α δ t (yOf a₀ t v) = v / α + δ := by
  have hs : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.2 ht
  have key : a₀ - Real.sqrt t * yOf a₀ t v = (v ^ 2)⁻¹ := by
    unfold yOf; field_simp; ring
  unfold radiusOf subst
  rw [key, Real.sqrt_inv, Real.sqrt_sq hv.le, inv_inv]

theorem yOf_mul_sqrt {a₀ v t : ℝ} (ht : 0 < t) :
    yOf a₀ t v * Real.sqrt t = a₀ - (v ^ 2)⁻¹ := by
  have hs : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.2 ht
  unfold yOf; field_simp

theorem subst_sq_inv {a₀ s Y : ℝ} (hu : 0 < a₀ - s * Y) :
    ((subst a₀ s Y) ^ 2)⁻¹ = a₀ - s * Y := by
  rw [subst, inv_pow, Real.sq_sqrt hu.le, inv_inv]

/-! ## 2. The chain's numbers -/

theorem sqrtT_eq {n : ℕ} (hn : 0 < n) {T : ℝ} (hT : T = 16 * Real.log n / (n : ℝ) ^ 2) :
    Real.sqrt T = 4 * Real.sqrt (Real.log n) / (n : ℝ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h := drift_eq hn hT
  field_simp at h ⊢
  linarith

/-- **The window is small.**  `log n · √T = 4(log n)^{3/2}/n ≤ 1/2`, from `HJ.log_cube_le`. -/
theorem logn_sqrtT_le {n : ℕ} (hn : 2073600 ≤ n) {T : ℝ}
    (hT : T = 16 * Real.log n / (n : ℝ) ^ 2) :
    Real.log n * Real.sqrt T ≤ 1 / 2 := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hlog : (1 : ℝ) ≤ Real.log n := one_le_log_of_three (by omega)
  have hTnn : 0 ≤ T := by rw [hT]; positivity
  have hcube : (Real.log n) ^ 3 ≤ 216 * Real.sqrt n := log_cube_le (by omega)
  have hsn : Real.sqrt n ≤ (n : ℝ) := by
    have h := Real.sqrt_le_sqrt (show (n : ℝ) ≤ (n : ℝ) ^ 2 by nlinarith)
    rwa [Real.sqrt_sq (by linarith : (0 : ℝ) ≤ (n : ℝ))] at h
  have hsn0 : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
  have h64 : 64 * (Real.log n) ^ 3 ≤ (n : ℝ) ^ 2 := by nlinarith
  have hsq : (Real.log n * Real.sqrt T) ^ 2 = 16 * (Real.log n) ^ 3 / (n : ℝ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hTnn, hT]; ring
  have hkey : (Real.log n * Real.sqrt T) ^ 2 ≤ 1 / 4 := by
    rw [hsq, div_le_iff₀ (by positivity)]; linarith
  have hx0 : 0 ≤ Real.log n * Real.sqrt T := mul_nonneg (by linarith) (Real.sqrt_nonneg _)
  nlinarith

/-- `a₀ = (1 − 1/n)⁻² ≤ 4` for `n ≥ 2` — `hgbound_chained`'s `hlow` needs it. -/
theorem params_a0_le_four {p n : ℕ} (P : Params p n) (hn : 2 ≤ n) : P.a0 ≤ 4 := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have h1 : (1 : ℝ) / 2 ≤ 1 - 1 / (n : ℝ) := by
    have : 1 / (n : ℝ) ≤ 1 / 2 := by rw [div_le_div_iff₀ hn0 (by norm_num)]; linarith
    linarith
  have hinv : (1 - 1 / (n : ℝ))⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have hinv0 : (0 : ℝ) ≤ (1 - 1 / (n : ℝ))⁻¹ := by positivity
  rw [P.a0_eq]; nlinarith

/-! ## 3. Lemma 4.3's constant, and the bound for `t ≥ t₀` -/

/-- `radiusOf a₀ α (√n/2) t 0`, written `t`-free. -/
noncomputable def rhoC (a₀ α : ℝ) (n : ℕ) : ℝ := (Real.sqrt a₀)⁻¹ / α + Real.sqrt n / 2

/-- `pieces_at_params`' constant: `K = e⁶ + e³(2/√(2π) + 2) + 2e³`. -/
noncomputable def Kc : ℝ :=
  Real.exp 6 + Real.exp 3 * (2 / Real.sqrt (2 * π) + 2) + 2 * Real.exp 3

/-- Lemma 4.3's per-`t` constant, `ρⁿ/(2n) + e^{1/2}K/(n·αⁿ)`. -/
noncomputable def C1c (a₀ α : ℝ) (n : ℕ) : ℝ :=
  rhoC a₀ α n ^ n / (2 * (n : ℝ)) + Real.exp (1 / 2) / ((n : ℝ) * α ^ n) * Kc

theorem rhoC_nonneg {a₀ α : ℝ} {n : ℕ} (hα : 0 < α) : 0 ≤ rhoC a₀ α n := by
  unfold rhoC; positivity

theorem C1c_nonneg {a₀ α : ℝ} {n : ℕ} (hα : 0 < α) : 0 ≤ C1c a₀ α n := by
  have hr : 0 ≤ rhoC a₀ α n := rhoC_nonneg hα
  refine add_nonneg (div_nonneg (pow_nonneg hr _) (by positivity)) ?_
  have hK : 0 ≤ Kc := by unfold Kc; positivity
  exact mul_nonneg (by positivity) hK

/-- **Lemma 4.3 at a single `t ≥ t₀ = 16/n²`,** with the window held at its `t = T` value. -/
theorem hgbound_at {a₀ α W T t : ℝ} {n : ℕ} (hn : 2073600 ≤ n)
    (hα : 0 < α) (ha₀ : 1 ≤ a₀) (ha₀4 : a₀ ≤ 4)
    (hdef : (n : ℝ) * (α * Real.sqrt n / 2) ≤ 1 / 4)
    (hT : T = 16 * Real.log n / (n : ℝ) ^ 2)
    (hWdef : W = radiusOf a₀ α (Real.sqrt n / 2) T (Real.log n))
    (ht0 : 16 / (n : ℝ) ^ 2 ≤ t) (htT : t ≤ T) :
    ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (y ^ (n - 1) * profile a₀ α W n t y)
      ≤ ENNReal.ofReal (C1c a₀ α n * Real.exp ((n : ℝ) ^ 2 * t / 8)) := by
  have hn0 : 0 < n := by omega
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hlog : (1 : ℝ) ≤ Real.log n := one_le_log_of_three (by omega)
  have hsl : (1 : ℝ) ≤ Real.sqrt (Real.log n) := one_le_sqrt_log (by omega)
  have hsT : Real.sqrt T = 4 * Real.sqrt (Real.log n) / (n : ℝ) := sqrtT_eq hn0 hT
  have hwinT : Real.log n * Real.sqrt T ≤ 1 / 2 := logn_sqrtT_le hn hT
  have hsTnn : (0 : ℝ) ≤ Real.sqrt T := Real.sqrt_nonneg _
  have hsT_half : Real.sqrt T ≤ 1 / 2 := by nlinarith
  have ht : 0 < t := lt_of_lt_of_le (by positivity) ht0
  have hst : Real.sqrt t ≤ Real.sqrt T := Real.sqrt_le_sqrt htT
  have hst_half : Real.sqrt t ≤ 1 / 2 := le_trans hst hsT_half
  have hstnn : (0 : ℝ) ≤ Real.sqrt t := Real.sqrt_nonneg _
  have hstpos : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.2 ht
  have hst_lb : 4 / (n : ℝ) ≤ Real.sqrt t := by
    have h := Real.sqrt_le_sqrt ht0
    rwa [show (16 : ℝ) / (n : ℝ) ^ 2 = (4 / (n : ℝ)) ^ 2 by rw [div_pow]; norm_num,
      Real.sqrt_sq (by positivity)] at h
  have hnst : (4 : ℝ) ≤ (n : ℝ) * Real.sqrt t := by
    rw [div_le_iff₀ hnpos, mul_comm] at hst_lb; exact hst_lb
  -- the reparameterised endpoint
  have hu : 0 < a₀ - Real.sqrt T * Real.log n := by nlinarith
  set v : ℝ := subst a₀ (Real.sqrt T) (Real.log n) with hv
  have hvpos : 0 < v := subst_pos hu
  have hWv : W = v / α + Real.sqrt n / 2 := by rw [hWdef, hv]; rfl
  set Yt : ℝ := yOf a₀ t v with hYt
  have hYtmul : Yt * Real.sqrt t = Real.sqrt T * Real.log n := by
    rw [hYt, yOf_mul_sqrt ht, hv, subst_sq_inv hu]; ring
  have hYt0 : 0 ≤ Yt := le_of_mul_le_mul_right
    (by rw [zero_mul, hYtmul]; exact mul_nonneg hsTnn (by linarith)) hstpos
  have hwin : Yt * Real.sqrt t ≤ 1 / 2 := by rw [hYtmul, mul_comm]; exact hwinT
  have hWdef2 : W = radiusOf a₀ α (Real.sqrt n / 2) t Yt := by
    rw [hYt, radiusOf_yOf ht hvpos]; exact hWv
  -- the window group
  have hSc : ∀ y ∈ Icc (0 : ℝ) Yt, 0 < a₀ - Real.sqrt t * y :=
    fun y hy => window_sub_pos ha₀ hy.2 hwin
  have hposw : ∀ y ∈ Ioc (0 : ℝ) Yt, 0 < 1 - Real.sqrt t * y :=
    fun y hy => window_one_sub_pos hy.2 hwin
  have hWY : ∀ y ∈ Ioc (0 : ℝ) Yt, radiusOf a₀ α (Real.sqrt n / 2) t y ≤ W := by
    intro y hy
    rw [hWdef2]
    exact radiusOf_le_end hα ht hYt0 hy.1.le hy.2 hSc
  have hρ : 0 ≤ radiusOf a₀ α (Real.sqrt n / 2) t 0 :=
    radiusOf_nonneg hα (by positivity) (lt_of_lt_of_le zero_lt_one ha₀)
  have hρW : radiusOf a₀ α (Real.sqrt n / 2) t 0 ≤ W := by
    rw [hWdef2]; exact radiusOf_le_end hα ht hYt0 le_rfl hYt0 hSc
  have hW0 : 0 ≤ W := le_trans hρ hρW
  have hlow : ∀ y ∈ Ioc (0 : ℝ) Yt, (1 : ℝ) / (2 * α) ≤ subst a₀ (Real.sqrt t) y / α := by
    intro y hy
    have hgz : 0 < a₀ - Real.sqrt t * y := window_sub_pos ha₀ hy.2 hwin
    have hle4 : a₀ - Real.sqrt t * y ≤ 4 := by nlinarith [mul_nonneg hstnn hy.1.le]
    have hs0 : 0 < Real.sqrt (a₀ - Real.sqrt t * y) := Real.sqrt_pos.2 hgz
    have hs2 : Real.sqrt (a₀ - Real.sqrt t * y) ≤ 2 := by
      have h := Real.sqrt_le_sqrt hle4
      rwa [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)] at h
    have hinv : (1 : ℝ) / 2 ≤ subst a₀ (Real.sqrt t) y := by
      rw [subst, ← one_div]
      exact one_div_le_one_div_of_le hs0 hs2
    rw [show (1 : ℝ) / (2 * α) = (1 / 2) / α by field_simp]
    gcongr
  -- the three pieces at the split point `A = n√t/4`
  have hA1 : (1 : ℝ) ≤ (n : ℝ) * Real.sqrt t / 4 := by linarith
  have hb2 : (2 : ℝ) ≤ (n : ℝ) * Real.sqrt t / 2 := by linarith
  have hA0 : (0 : ℝ) ≤ (n : ℝ) * Real.sqrt t / 4 := by positivity
  have key : (n : ℝ) * t / 4 ≤ Real.sqrt T * Real.log n := by
    rw [hsT]
    have hn2t : (n : ℝ) ^ 2 * t ≤ 16 * Real.log n := by
      have h : t ≤ 16 * Real.log n / (n : ℝ) ^ 2 := hT ▸ htT
      rw [le_div_iff₀ (by positivity)] at h
      nlinarith [h]
    have h16 : 16 * Real.log n ≤ 16 * Real.sqrt (Real.log n) * Real.log n := by nlinarith
    rw [div_mul_eq_mul_div, le_div_iff₀ hnpos]
    nlinarith [hn2t, h16]
  have hAY : (n : ℝ) * Real.sqrt t / 4 ≤ Yt := by
    refine le_of_mul_le_mul_right ?_ hstpos
    have hss : (n : ℝ) * Real.sqrt t / 4 * Real.sqrt t = (n : ℝ) * t / 4 := by
      rw [div_mul_eq_mul_div, mul_assoc, Real.mul_self_sqrt ht.le]
    rw [hss, hYtmul]
    exact key
  have hjunkT : Real.log n * Real.sqrt T
      + ((n : ℝ) + 2) / 2 * (Real.log n * Real.sqrt T) ^ 2 ≤ 3 :=
    junk_endpoint_le_three (t := T) hn (le_of_eq hsT)
  have hendY : Yt * Real.sqrt t + ((n : ℝ) + 2) / 2 * (Yt * Real.sqrt t) ^ 2 ≤ 3 := by
    rw [hYtmul, mul_comm (Real.sqrt T)]; exact hjunkT
  have hJ2 : ∀ y ∈ Ioc (1 : ℝ) ((n : ℝ) * Real.sqrt t / 4),
      y * Real.sqrt t + ((n : ℝ) + 2) / 2 * (y * Real.sqrt t) ^ 2 ≤ 3 :=
    fun y hy => junk_le_of_endpoint hendY (le_trans zero_le_one hy.1.le) (le_trans hy.2 hAY)
  have hJ3 : ∀ y ∈ Ioc ((n : ℝ) * Real.sqrt t / 4) Yt,
      y * Real.sqrt t + ((n : ℝ) + 2) / 2 * (y * Real.sqrt t) ^ 2 ≤ 3 :=
    fun y hy => junk_le_of_endpoint hendY (le_trans hA0 hy.1.le) hy.2
  have hpieces := pieces_at_params (n := n) hn0 ht.le hst_half hA1 hAY hwin hb2
    (le_of_eq (by ring)) (le_of_eq (by ring)) hJ2 hJ3
  -- chain
  have hchained := hgbound_chained hn0 hα ht ha₀ hYt0 hW0 hdef hWdef2 hSc hlow hposw hWY hρ hρW
    (integrableOn_shell_lhs hα (by linarith) hwin hWY hW0)
    (integrableOn_shell_rhs (α := α) hwin) hpieces
  have hnorm := hgbound_normalised hρ ht.le hchained
  rw [radiusOf_zero_eq] at hnorm
  unfold C1c rhoC Kc
  exact hnorm


/-! ## 4. `hgbound'` — the bound uniformly in `t ∈ (0, T]` -/

theorem W_nonneg {a₀ α W T : ℝ} {n : ℕ} (hn : 2073600 ≤ n) (hα : 0 < α) (ha₀ : 1 ≤ a₀)
    (hT : T = 16 * Real.log n / (n : ℝ) ^ 2)
    (hWdef : W = radiusOf a₀ α (Real.sqrt n / 2) T (Real.log n)) : 0 ≤ W := by
  have hwinT : Real.log n * Real.sqrt T ≤ 1 / 2 := logn_sqrtT_le hn hT
  have hu : 0 < a₀ - Real.sqrt T * Real.log n := by rw [mul_comm]; linarith
  rw [hWdef, radiusOf]
  exact add_nonneg (div_nonneg (subst_pos hu).le hα.le) (by positivity)

/-- **Lemma 4.3, uniformly in `t`.**  The `t ≥ t₀` branch is `hgbound_at`; below `t₀ = 16/n²` the
profile's monotonicity in `t` reduces to the value at `t₀`, where `e^{n²t₀/8} = e²`.  One constant
`e²·C₁` serves both. -/
theorem hgbound'_of_chain {a₀ α W T : ℝ} {n : ℕ} (hn : 2073600 ≤ n)
    (hα : 0 < α) (ha₀ : 1 ≤ a₀) (ha₀4 : a₀ ≤ 4)
    (hdef : (n : ℝ) * (α * Real.sqrt n / 2) ≤ 1 / 4)
    (hT : T = 16 * Real.log n / (n : ℝ) ^ 2)
    (hWdef : W = radiusOf a₀ α (Real.sqrt n / 2) T (Real.log n)) :
    ∀ t ∈ Ioc (0 : ℝ) T,
      ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (y ^ (n - 1) * profile a₀ α W n t y)
        ≤ ENNReal.ofReal (Real.exp 2 * C1c a₀ α n * Real.exp ((n : ℝ) ^ 2 / 8 * t)) := by
  intro t ht
  have hn0 : 0 < n := by omega
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hlog : (1 : ℝ) ≤ Real.log n := one_le_log_of_three (by omega)
  have hC0 : 0 ≤ C1c a₀ α n := C1c_nonneg hα
  have he1 : (1 : ℝ) ≤ Real.exp ((n : ℝ) ^ 2 / 8 * t) :=
    Real.one_le_exp (mul_nonneg (by positivity) ht.1.le)
  have he2 : (1 : ℝ) ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
  have ht0T : 16 / (n : ℝ) ^ 2 ≤ T := by
    rw [hT, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  by_cases hbig : 16 / (n : ℝ) ^ 2 ≤ t
  · refine le_trans (hgbound_at hn hα ha₀ ha₀4 hdef hT hWdef hbig ht.2)
      (ENNReal.ofReal_le_ofReal ?_)
    calc C1c a₀ α n * Real.exp ((n : ℝ) ^ 2 * t / 8)
        = 1 * (C1c a₀ α n * Real.exp ((n : ℝ) ^ 2 / 8 * t)) := by
          rw [show (n : ℝ) ^ 2 * t / 8 = (n : ℝ) ^ 2 / 8 * t by ring]; ring
      _ ≤ Real.exp 2 * (C1c a₀ α n * Real.exp ((n : ℝ) ^ 2 / 8 * t)) := by
          gcongr
      _ = Real.exp 2 * C1c a₀ α n * Real.exp ((n : ℝ) ^ 2 / 8 * t) := by ring
  · push Not at hbig
    have hmono : ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (y ^ (n - 1) * profile a₀ α W n t y)
        ≤ ∫⁻ y in Ioi (0 : ℝ),
            ENNReal.ofReal (y ^ (n - 1) * profile a₀ α W n (16 / (n : ℝ) ^ 2) y) := by
      refine lintegral_mono_ae ?_
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with y hy
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
        (profile_mono_time ht.1 hbig.le y) (pow_nonneg (le_of_lt hy) _))
    refine le_trans hmono (le_trans (hgbound_at hn hα ha₀ ha₀4 hdef hT hWdef le_rfl ht0T)
      (ENNReal.ofReal_le_ofReal ?_))
    rw [show (n : ℝ) ^ 2 * (16 / (n : ℝ) ^ 2) / 8 = 2 by field_simp; norm_num]
    calc C1c a₀ α n * Real.exp 2 = Real.exp 2 * C1c a₀ α n * 1 := by ring
      _ ≤ Real.exp 2 * C1c a₀ α n * Real.exp ((n : ℝ) ^ 2 / 8 * t) := by
          gcongr

/-! ## 5. Lemma 4.3's Bochner output — `Params.radial_bound` -/

/-- **Lemma 4.3, as `Params.radial_bound`.**  Tonelli over `(0,T]` turns the uniform fixed-`t`
bound into the radial bound the chain's `Params` asks for, with
`C = e²·C₁·(8 − 8/n²)` — the `t`-integral `∫₀ᵀ e^{n²t/8} dt = 8 − 8/n²` is exact, so the `n²`
of the horizon cancels the `n⁻²` of the exponent and the constant is absolute. -/
theorem radial_bound_of_chain {a₀ α W T : ℝ} {n : ℕ} (hn : 2073600 ≤ n)
    (hα : 0 < α) (ha₀ : 1 ≤ a₀) (ha₀4 : a₀ ≤ 4)
    (hdef : (n : ℝ) * (α * Real.sqrt n / 2) ≤ 1 / 4)
    (hT : T = 16 * Real.log n / (n : ℝ) ^ 2)
    (hWdef : W = radiusOf a₀ α (Real.sqrt n / 2) T (Real.log n)) :
    ∫ y in Ioi (0 : ℝ), y ^ (n - 1) * (∫ t in Ioc (0 : ℝ) T, profile a₀ α W n t y)
      ≤ Real.exp 2 * C1c a₀ α n * (8 - 8 / (n : ℝ) ^ 2) := by
  have hn0 : 0 < n := by omega
  have hC0 : 0 ≤ Real.exp 2 * C1c a₀ α n := mul_nonneg (Real.exp_pos 2).le (C1c_nonneg hα)
  have hT0 : (0 : ℝ) ≤ T := hT ▸ T_nonneg hn0
  have hW0 : 0 ≤ W := W_nonneg hn hα ha₀ hT hWdef
  have hgmeas : AEMeasurable
      (Function.uncurry (fun y t : ℝ =>
        ENNReal.ofReal (y ^ (n - 1) * profile a₀ α W n t y)))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioc (0 : ℝ) T))) :=
    (((measurable_fst.pow_const (n - 1)).mul
      (measurable_profile_uncurry.comp measurable_swap)).ennreal_ofReal).aemeasurable
  refine radial_bound_of_lintegral
    (fun r => integral_nonneg_of_nonneg (fun t r => profile_nonneg t r) r)
    (mul_nonneg hC0 (eight_sub_nonneg hn0))
    (integrableOn_profile_radial_t hW0 hT0) ?_
  have hcongr : ∫⁻ y in Ioi (0 : ℝ),
        ENNReal.ofReal (y ^ (n - 1) * ∫ t in Ioc (0 : ℝ) T, profile a₀ α W n t y)
      = ∫⁻ y in Ioi (0 : ℝ), ∫⁻ t in Ioc (0 : ℝ) T,
          ENNReal.ofReal (y ^ (n - 1) * profile a₀ α W n t y) :=
    setLIntegral_congr_fun measurableSet_Ioi (fun y hy =>
      (lintegral_t_ofReal (n := n) (le_of_lt hy) (fun t r => profile_nonneg t r)
        (integrableOn_profile_time y)).symm)
  rw [hcongr]
  exact lintegral_radial_t_le hn0 hT hT0 hC0 _ hgmeas
    (hgbound'_of_chain hn hα ha₀ ha₀4 hdef hT hWdef)

/-! ### The Euclidean integrability of the `t`-integrated profile

`Params.integrable` asks for integrability on `EuclideanSpace ℝ (Fin n)`, not on the radius.  The
profile is bounded by `1/2` and vanishes past `W`, so the `t`-integral is bounded by `T/2` with
support in a closed ball — no polar coordinates needed. -/

theorem profile_zero_int {a₀ α W T : ℝ} {n : ℕ} {r : ℝ} (hr : W < r) :
    (∫ t in Ioc (0 : ℝ) T, profile a₀ α W n t r) = 0 := by
  simp [profile_zero_of_gt hr]

theorem stronglyMeasurable_int {a₀ α W T : ℝ} {n : ℕ} :
    StronglyMeasurable (fun r : ℝ => ∫ t in Ioc (0 : ℝ) T, profile a₀ α W n t r) :=
  ((measurable_profile_uncurry (a₀ := a₀) (α := α) (W := W) (n := n)).comp
    measurable_swap).stronglyMeasurable.integral_prod_right'

/-- **`Params.integrable`, discharged.** -/
theorem integrable_radial_euclidean {a₀ α W T : ℝ} {n : ℕ} (hT : 0 ≤ T) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      ∫ t in Ioc (0 : ℝ) T, profile a₀ α W n t ‖x‖) := by
  have hsm : StronglyMeasurable (fun x : EuclideanSpace ℝ (Fin n) =>
      ∫ t in Ioc (0 : ℝ) T, profile a₀ α W n t ‖x‖) :=
    stronglyMeasurable_int.comp_measurable (continuous_norm.measurable)
  have hbnd : ∀ x : EuclideanSpace ℝ (Fin n),
      ‖∫ t in Ioc (0 : ℝ) T, profile a₀ α W n t ‖x‖‖ ≤ 1 / 2 * T := by
    intro x
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0 : ℝ) T)
      (C := 1 / 2) (f := fun t => profile a₀ α W n t ‖x‖)
      (by simp [Real.volume_Ioc]) (fun t _ => norm_profile_le t ‖x‖)
    simpa [Real.volume_Ioc, max_eq_left hT] using h
  have h1 : IntegrableOn (fun x : EuclideanSpace ℝ (Fin n) =>
      ∫ t in Ioc (0 : ℝ) T, profile a₀ α W n t ‖x‖) (Metric.closedBall 0 W) :=
    integrableOn_of_bounded' measurableSet_closedBall
      (measure_closedBall_lt_top).ne hsm.aestronglyMeasurable (M := 1 / 2 * T)
      (fun x _ => hbnd x)
  have h2 : IntegrableOn (fun x : EuclideanSpace ℝ (Fin n) =>
      ∫ t in Ioc (0 : ℝ) T, profile a₀ α W n t ‖x‖) (Metric.closedBall 0 W)ᶜ := by
    refine (integrableOn_zero (μ := volume)
      (s := (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) W)ᶜ)).congr_fun ?_
      measurableSet_closedBall.compl
    intro x hx
    exact (profile_zero_int
      (by simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hx)).symm
  rw [← integrableOn_univ, ← union_compl_self (Metric.closedBall
    (0 : EuclideanSpace ℝ (Fin n)) W)]
  exact h1.union h2

/-! ## 6. `Params''` is empty — why the hand-off needs a different structure

`Params'.f_eq` says `f = profile … T`; report 33's `Params''.f_eq'` says `f` is the `t`-integral of
the same profile.  Both are equalities of functions, and they disagree at `r = 0`, where the
profile is `1/2` at every `t` and the `t`-integral is `T/2`.  So a `Params''` forces `T = 1`,
while `T = 16·log n/n² < 1` for every `n ≥ 2 073 600`.  Hence `Params''` has no inhabitants, and
report 33's `weight_bound_of_params''` and `lemma43_input`, though true, are vacuous. -/

theorem params''_elim {p n : ℕ} (P : Params'' p n) : False := by
  have hn : 2073600 ≤ n := P.n_large
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hT : P.T = 16 * Real.log n / (n : ℝ) ^ 2 := by rw [P.T_eq]; rfl
  have hlog : (1 : ℝ) ≤ Real.log n := one_le_log_of_three (by omega)
  have hTpos : 0 < P.T := by rw [hT]; positivity
  have hW0 : 0 ≤ P.windowRadius :=
    le_trans P.radius_nonneg (P.radius_le hTpos le_rfl P.Y_nonneg)
  have hsn : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.2 hnpos
  have hprof : ∀ t : ℝ, profile P.a0 P.alpha P.windowRadius n t 0 = 1 / 2 := by
    intro t
    unfold profile
    rw [ite_eq_right (not_lt.2 hW0), ite_eq_left (by nlinarith [P.alpha_pos])]
  have h1 : P.f 0 = 1 / 2 := by rw [P.f_eq]; exact hprof P.T
  have h2 : P.f 0 = P.T / 2 := by
    rw [P.f_eq']
    simp only [hprof]
    have hvol : (volume.real (Ioc (0 : ℝ) P.T)) = P.T := by
      rw [measureReal_def, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal hTpos.le]
    rw [setIntegral_const, hvol, smul_eq_mul]
    ring
  have hT1 : P.T = 1 := by rw [h1] at h2; linarith
  have hlogle : Real.log n ≤ (n : ℝ) - 1 := Real.log_le_sub_one_of_pos hnpos
  have hTlt : P.T < 1 := by
    rw [hT, div_lt_one (by positivity)]
    nlinarith
  linarith

/-! ## 7. The chain's input, and `Params` with Lemma 4.3 discharged -/

/-- Klartag's `a₀ = (1 − 1/n)⁻²`, p. 21 eq. (61). -/
noncomputable def a0C (n : ℕ) : ℝ := (1 - 1 / (n : ℝ))⁻¹ ^ 2

/-- The window, at the endpoint `HJ.junk_endpoint_le_three` is proved for. -/
noncomputable def windowC (α : ℝ) (n : ℕ) : ℝ :=
  radiusOf (a0C n) α (Real.sqrt n / 2) (ChainDrift.horizon n) (Real.log n)

/-- Lemma 4.3's radial profile: the `t`-integrated, worst-point-widened profile. -/
noncomputable def fC (α : ℝ) (n : ℕ) : ℝ → ℝ := fun r =>
  ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n), profile (a0C n) α (windowC α n) n t r

/-- Lemma 4.3's per-`t` constant, with the small-`t` branch's `e²`. -/
noncomputable def C1C (α : ℝ) (n : ℕ) : ℝ := Real.exp 2 * C1c (a0C n) α n

theorem horizon_eq (n : ℕ) : ChainDrift.horizon n = 16 * Real.log n / (n : ℝ) ^ 2 := rfl

theorem a0C_ge_one {n : ℕ} (hn : 2 ≤ n) : 1 ≤ a0C n := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have h1 : (0 : ℝ) < 1 - 1 / (n : ℝ) := by
    have : 1 / (n : ℝ) ≤ 1 / 2 := by rw [div_le_div_iff₀ hn0 (by norm_num)]; linarith
    linarith
  have hinv : (1 : ℝ) ≤ (1 - 1 / (n : ℝ))⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) h1]; simp
  unfold a0C; nlinarith

theorem a0C_le_four {n : ℕ} (hn : 2 ≤ n) : a0C n ≤ 4 := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have h1 : (1 : ℝ) / 2 ≤ 1 - 1 / (n : ℝ) := by
    have : 1 / (n : ℝ) ≤ 1 / 2 := by rw [div_le_div_iff₀ hn0 (by norm_num)]; linarith
    linarith
  have hinv : (1 - 1 / (n : ℝ))⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have hinv0 : (0 : ℝ) ≤ (1 - 1 / (n : ℝ))⁻¹ := by positivity
  unfold a0C; nlinarith

theorem C1c_pos {a₀ α : ℝ} {n : ℕ} (hn : 0 < n) (hα : 0 < α) (ha₀ : 0 < a₀) :
    0 < C1c a₀ α n := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hr : 0 < rhoC a₀ α n := by
    unfold rhoC
    have : (0 : ℝ) < (Real.sqrt a₀)⁻¹ / α := by positivity
    positivity
  have h1 : 0 < rhoC a₀ α n ^ n / (2 * (n : ℝ)) := by positivity
  have hK : 0 ≤ Kc := by unfold Kc; positivity
  have h2 : 0 ≤ Real.exp (1 / 2) / ((n : ℝ) * α ^ n) * Kc :=
    mul_nonneg (by positivity) hK
  unfold C1c; linarith

theorem C1C_pos {α : ℝ} {n : ℕ} (hn : 2 ≤ n) (hα : 0 < α) : 0 < C1C α n :=
  mul_pos (Real.exp_pos 2)
    (C1c_pos (by omega) hα (lt_of_lt_of_le zero_lt_one (a0C_ge_one hn)))

/-- **The chain's input.**  `ChainDataInst.Params` with Lemma 4.3's block removed: exactly what
the discharge must supply.  `a0`, `T`, `N`, `h`, `windowRadius`, `f`, `C` and `theta` are all
computed by `params_of_chain`; the Markov field reduces to the arithmetic statement `arith`. -/
structure ChainInput (p n : ℕ) where
  alpha : ℝ
  alpha_pos : 0 < alpha
  alpha_norm : alpha ^ n * ((p ^ (n - 1) : ℕ) : ℝ) = kappa n
  R : ℝ
  R_nonneg : 0 ≤ R
  R_scaled : alpha * R ≤ 1 - 1 / (n : ℝ)
  R_lt_p : R < (p : ℝ)
  tiling_defect : (n : ℝ) * (alpha * Real.sqrt n / 2) ≤ 1 / 4
  window_lt_p : windowC alpha n < (p : ℝ)
  w : (Fin n → ℤ) → ℝ≥0∞
  supp : Finset (Fin n → ℤ)
  supp_ne_zero : ∀ y ∈ supp, y ≠ 0
  supp_radius : ∀ y ∈ supp, ‖toE n y‖ ≤ windowC alpha n
  dom : ∀ y ∈ supp, ∀ x ∈ cube (toE n y), w y ≤ ENNReal.ofReal (fC alpha n ‖x‖)
  arith : (n : ℝ) * kappa n * ((p : ℝ) - 1) * (8 - 8 / (n : ℝ) ^ 2) < 8 * ((p : ℝ) ^ n - 1)

/-- **`Params` from the chain's input** — Lemma 4.3 discharged, every field supplied. -/
noncomputable def params_of_chain {p n : ℕ} [Fact (Nat.Prime p)] (hn : 2073600 ≤ n)
    (I : ChainInput p n) : Params p n where
  dim_pos := by omega
  alpha := I.alpha
  alpha_pos := I.alpha_pos
  alpha_norm := I.alpha_norm
  a0 := a0C n
  a0_eq := rfl
  R := I.R
  R_nonneg := I.R_nonneg
  R_scaled := I.R_scaled
  R_lt_p := I.R_lt_p
  tiling_defect := I.tiling_defect
  T := ChainDrift.horizon n
  T_eq := rfl
  N := ChainDrift.numSteps n 5
  N_eq := rfl
  h := ChainDrift.stepSize n 5
  h_eq := rfl
  windowRadius := windowC I.alpha n
  window_lt_p := I.window_lt_p
  f := fC I.alpha n
  f_nonneg := fun r => integral_nonneg_of_nonneg (fun t r => profile_nonneg t r) r
  w := I.w
  supp := I.supp
  supp_ne_zero := I.supp_ne_zero
  supp_radius := I.supp_radius
  dom := I.dom
  integrable := integrable_radial_euclidean (T_nonneg (by omega))
  C := C1C I.alpha n * (8 - 8 / (n : ℝ) ^ 2)
  radial_bound :=
    radial_bound_of_chain hn I.alpha_pos (a0C_ge_one (by omega)) (a0C_le_four (by omega))
      I.tiling_defect (horizon_eq n) rfl
  theta := ENNReal.ofReal (16 * C1C I.alpha n)
  theta_ne_zero := by
    have := C1C_pos (α := I.alpha) (n := n) (by omega) I.alpha_pos
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    linarith
  theta_ne_top := ENNReal.ofReal_ne_top
  markov :=
    markov_of_arith (by omega) (Nat.Prime.one_lt (Fact.out)).le
      (Nat.one_lt_pow (by omega) (Nat.Prime.one_lt (Fact.out)))
      (C1C_pos (α := I.alpha) (n := n) (by omega) I.alpha_pos) I.arith

/-- `ChainData` from the chain's input. -/
noncomputable def chainData_of_chain {p n : ℕ} [Fact (Nat.Prime p)] [NeZero p]
    (hn : 2073600 ≤ n) (I : ChainInput p n) : ChainData p n :=
  chainData_of_params (params_of_chain hn I)

/-- §5's line `g`, from the chain's input. -/
theorem exists_good_line_of_chain {p n : ℕ} [Fact (Nat.Prime p)] [NeZero p]
    (hn : 2073600 ≤ n) (I : ChainInput p n) :
    ∃ g : Fin n → ZMod p, g ≠ 0 ∧
      (∀ y : Fin n → ℤ, y ≠ 0 → ‖toE n y‖ ≤ I.R → y ∉ latZ p n g) ∧
      ∑ y ∈ I.supp.filter (fun y => y ∈ latZ p n g), I.w y < ENNReal.ofReal (16 * C1C I.alpha n) :=
  exists_good_line_of_params (params_of_chain hn I)

/-- **The hand-off.**  `Threshold2.remaining_of_lemma43` fed from the chain's input alone:
Lemma 4.3 contributes `a0`, `T`, `windowRadius`, `f`, `C`, `radial_bound` and `theta`, and what
remains is `ChainInput` plus the chain's own `ChainOutput`. -/
theorem lemma43_input_of_chain {c₀ : ℝ} (hc₀ : 0 < c₀)
    (H : ∀ m : ℕ, Threshold2.n₁ ≤ m →
      ∃ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p) (I : ChainInput p (m + 1)),
        ∀ g : Fin (m + 1) → ZMod p, g ≠ 0 →
          (∀ y : Fin (m + 1) → ℤ, y ≠ 0 → ‖toE (m + 1) y‖ ≤ I.R → y ∉ latZ p (m + 1) g) →
          Assembly.ChainOutput I.alpha g c₀) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      let V := EuclideanSpace ℝ (Fin (n + 1))
      ∃ φ : V →ₗ[ℝ] V, let E := φ '' Metric.ball (0 : V) 1
        (MeasureTheory.volume E : EReal) = c * n ^ 2 ∧
        {v ∈ E | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} :=
  Threshold2.remaining_of_lemma43 hc₀ (fun m hm => by
    obtain ⟨p, hp, hp0, I, h⟩ := H m hm
    have hm' : 2073600 ≤ m := by simpa [Threshold2.n₁] using hm
    exact ⟨p, hp, hp0, params_of_chain (by omega) I, h⟩)

end Submission.L10

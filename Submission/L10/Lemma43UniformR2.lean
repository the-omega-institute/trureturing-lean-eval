/-
Gate L-10 (`klartag_packing`), brief 85a part C.

**Lemma 4.3 at the generic window `WindowR2.windowR2`.**

`Lemma43UniformR`'s analytic pieces — `pieces_four`, `far_numerics`, `ct_le`, `cs_le`,
`junk_endpoint_two_log`, `C1cR`, `KcR`, `C1R`, `C1R_le` — are general in the window and are
imported, not copied.  What names `WindowR.windowR`, and so has to be re-proved here, is the
chain from `hgbound_at'` to `params_of_chainR`.  The substitution is exactly
`mR → mR2`, `YR → YR2`, `reachNum → reachNum2`, `windowR → windowR2`; every fact those proofs
used about `mR` (`mR_ge`, `mR_pos`, `mR_lt_one`, `sqrtT_mul_YR`, `reachNum_eq`) has a `WindowR2`
twin, and `mR2_ge` is `le_refl`.

The one lemma that is not a rename is `two_logn_sqrtT_le_gap2`: at the adopted reach it needed
`2·log n·√T ≤ a0C − mAdopted`, an inequality about `r₀ + c₃η`; at the generic window the gap is
exactly `1/2`, so it is `logn_sqrtT_le_quarter` doubled.

**Kill rule 2.**  The constant is unchanged — `C1R α n = e²·C1cR (a0C n) α n`, the same value as
at the adopted reach, and the exponent `e^{n²t/8}` and the exact `∫₀ᵀ = 8 − 8/n²` are untouched.
Widening the window costs nothing in `C`; it only widens the support the profile must dominate.
-/
import Submission.L10.Lemma43UniformR
import Submission.L10.WindowR2

namespace Submission.L10.Lemma43R2

open MeasureTheory Set Real Submission.L10 Submission.L10.Lemma43R
open scoped ENNReal NNReal

/-! ## 0. The junk-endpoint gap at the generic window -/

/-- At the generic window the reach gap is exactly `1/2`, so the split point `2·log n` sits below
the endpoint by `logn_sqrtT_le_quarter` alone. -/
theorem two_logn_sqrtT_le_gap2 {n : ℕ} (hn : 2073600 ≤ n) :
    2 * Real.log n * Real.sqrt (ChainDrift.horizon n) ≤ a0C n - WindowR2.mR2 n := by
  have h := logn_sqrtT_le_quarter hn
  rw [WindowR2.mR2]
  linarith

/-! ## 1. Lemma 4.3 at a single `t ≥ 16/n²`, at the generic window -/

set_option maxHeartbeats 1000000 in
/-- **Lemma 4.3 at a single `t ≥ 16/n²`, at the reach window.** -/
theorem hgbound_at2 {α W t : ℝ} {n : ℕ} (hn : 2073600 ≤ n) (hα : 0 < α)
    (hdef : (n : ℝ) * (α * Real.sqrt n / 2) ≤ 1 / 4)
    (hWdef : W = WindowR2.windowR2 α n)
    (ht0 : 16 / (n : ℝ) ^ 2 ≤ t) (htT : t ≤ ChainDrift.horizon n) :
    ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (y ^ (n - 1) * profile (a0C n) α W n t y)
      ≤ ENNReal.ofReal (C1cR (a0C n) α n * Real.exp ((n : ℝ) ^ 2 * t / 8)) := by
  have hn3 : 3 ≤ n := by omega
  have hn0 : 0 < n := by omega
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hlog : (6 : ℝ) ≤ Real.log n := six_le_log hn
  have hsl : (1 : ℝ) ≤ Real.sqrt (Real.log n) := one_le_sqrt_log (by omega)
  have hT : ChainDrift.horizon n = 16 * Real.log n / (n : ℝ) ^ 2 := horizon_eq n
  have hsT : Real.sqrt (ChainDrift.horizon n) = 4 * Real.sqrt (Real.log n) / (n : ℝ) :=
    sqrtT_eq hn0 hT
  have hTpos : 0 < ChainDrift.horizon n := horizon_pos hn3
  have hsTpos : 0 < Real.sqrt (ChainDrift.horizon n) := Real.sqrt_pos.2 hTpos
  have ht : 0 < t := lt_of_lt_of_le (by positivity) ht0
  have hst : Real.sqrt t ≤ Real.sqrt (ChainDrift.horizon n) := Real.sqrt_le_sqrt htT
  have hstpos : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.2 ht
  have hstnn : (0 : ℝ) ≤ Real.sqrt t := hstpos.le
  have hst2 : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  have hquarter : Real.log n * Real.sqrt (ChainDrift.horizon n) ≤ 1 / 4 :=
    logn_sqrtT_le_quarter hn
  have hsT_half : Real.sqrt (ChainDrift.horizon n) ≤ 1 / 4 := by nlinarith [hsTpos]
  have hst_half : Real.sqrt t ≤ 1 / 2 := by linarith
  have hst_lb : 4 / (n : ℝ) ≤ Real.sqrt t := by
    have h := Real.sqrt_le_sqrt ht0
    rwa [show (16 : ℝ) / (n : ℝ) ^ 2 = (4 / (n : ℝ)) ^ 2 by rw [div_pow]; norm_num,
      Real.sqrt_sq (by positivity)] at h
  have hnst : (4 : ℝ) ≤ (n : ℝ) * Real.sqrt t := by
    rw [div_le_iff₀ hnpos, mul_comm] at hst_lb; exact hst_lb
  -- the reach endpoint
  have hmRpos : 0 < WindowR2.mR2 n := WindowR2.mR2_pos hn
  have hgap : Real.sqrt (ChainDrift.horizon n) * WindowR2.YR2 n = a0C n - WindowR2.mR2 n :=
    WindowR2.sqrtT_mul_YR2 hn3
  have hu : 0 < a0C n - Real.sqrt (ChainDrift.horizon n) * WindowR2.YR2 n := by
    rw [hgap]; linarith [hmRpos]
  set v : ℝ := WindowR2.reachNum2 n with hv
  have hvdef : v = subst (a0C n) (Real.sqrt (ChainDrift.horizon n)) (WindowR2.YR2 n) := rfl
  have hvpos : 0 < v := by rw [hvdef]; exact subst_pos hu
  have hWv : W = v / α + Real.sqrt n / 2 := by rw [hWdef]; exact WindowR2.windowR2_eq α n
  set Yt : ℝ := yOf (a0C n) t v with hYt
  have hYtmul : Yt * Real.sqrt t = a0C n - WindowR2.mR2 n := by
    rw [hYt, yOf_mul_sqrt ht, hvdef, subst_sq_inv hu, hgap]; ring
  have hY1 : Yt * Real.sqrt t ≤ 1 / 2 := by
    rw [hYtmul]; linarith [WindowR2.mR2_ge n]
  have hYt0 : 0 ≤ Yt := le_of_mul_le_mul_right
    (by rw [zero_mul, hYtmul]; linarith [WindowR2.mR2_lt_one hn, a0C_ge_one (by omega : 2 ≤ n)])
    hstpos
  have hWdef2 : W = radiusOf (a0C n) α (Real.sqrt n / 2) t Yt := by
    rw [hYt, radiusOf_yOf ht hvpos]; exact hWv
  -- the split point
  set Ymid : ℝ := 2 * Real.log n * Real.sqrt (ChainDrift.horizon n) / Real.sqrt t with hYmid
  have hYmidmul : Ymid * Real.sqrt t = 2 * Real.log n * Real.sqrt (ChainDrift.horizon n) := by
    rw [hYmid, div_mul_cancel₀ _ (ne_of_gt hstpos)]
  have hYmid0 : 0 < Ymid := by
    rw [hYmid]; positivity
  have hYmidhalf : Ymid * Real.sqrt t ≤ 1 / 2 := by rw [hYmidmul]; linarith
  have hmidY1 : Ymid ≤ Yt := by
    refine le_of_mul_le_mul_right ?_ hstpos
    rw [hYmidmul, hYtmul]
    exact two_logn_sqrtT_le_gap2 hn
  -- the window group at the reach endpoint
  have ha1 : (1 : ℝ) ≤ a0C n := a0C_ge_one (by omega)
  have hSc : ∀ y ∈ Icc (0 : ℝ) Yt, 0 < a0C n - Real.sqrt t * y :=
    fun y hy => window_sub_pos ha1 hy.2 hY1
  have hposw : ∀ y ∈ Ioc (0 : ℝ) Yt, 0 < 1 - Real.sqrt t * y :=
    fun y hy => window_one_sub_pos hy.2 hY1
  have hWY : ∀ y ∈ Ioc (0 : ℝ) Yt, radiusOf (a0C n) α (Real.sqrt n / 2) t y ≤ W := by
    intro y hy
    rw [hWdef2]
    exact radiusOf_le_end hα ht hYt0 hy.1.le hy.2 hSc
  have hρ : 0 ≤ radiusOf (a0C n) α (Real.sqrt n / 2) t 0 :=
    radiusOf_nonneg hα (by positivity) (lt_of_lt_of_le zero_lt_one ha1)
  have hρW : radiusOf (a0C n) α (Real.sqrt n / 2) t 0 ≤ W := by
    rw [hWdef2]; exact radiusOf_le_end hα ht hYt0 le_rfl hYt0 hSc
  have hW0 : 0 ≤ W := le_trans hρ hρW
  have ha4 : a0C n ≤ 4 := a0C_le_four (by omega)
  have hlow : ∀ y ∈ Ioc (0 : ℝ) Yt, (1 : ℝ) / (2 * α) ≤ subst (a0C n) (Real.sqrt t) y / α := by
    intro y hy
    have hgz : 0 < a0C n - Real.sqrt t * y := window_sub_pos ha1 hy.2 hY1
    have hle4 : a0C n - Real.sqrt t * y ≤ 4 := by nlinarith [mul_nonneg hstnn hy.1.le]
    have hs0 : 0 < Real.sqrt (a0C n - Real.sqrt t * y) := Real.sqrt_pos.2 hgz
    have hs2 : Real.sqrt (a0C n - Real.sqrt t * y) ≤ 2 := by
      have h := Real.sqrt_le_sqrt hle4
      rwa [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)] at h
    have hinv : (1 : ℝ) / 2 ≤ subst (a0C n) (Real.sqrt t) y := by
      rw [subst, ← one_div]
      exact one_div_le_one_div_of_le hs0 hs2
    rw [show (1 : ℝ) / (2 * α) = (1 / 2) / α by field_simp]
    gcongr
  -- the split point's numeric facts
  have hA1 : (1 : ℝ) ≤ (n : ℝ) * Real.sqrt t / 4 := by linarith
  have hb2 : (2 : ℝ) ≤ (n : ℝ) * Real.sqrt t / 2 := by linarith
  have hA0 : (0 : ℝ) ≤ (n : ℝ) * Real.sqrt t / 4 := by positivity
  have hL12 : (12 : ℝ) ≤ Real.log n := twelve_le_log hn
  have hsl12 : Real.sqrt (Real.log n) ^ 2 = Real.log n := Real.sq_sqrt (by linarith)
  have hslpos : (0 : ℝ) < Real.sqrt (Real.log n) := Real.sqrt_pos.2 (by linarith)
  have hsl3 : (3 : ℝ) ≤ Real.sqrt (Real.log n) := by nlinarith [hsl12, hslpos, hL12]
  have hAY : (n : ℝ) * Real.sqrt t / 4 ≤ Ymid := by
    refine le_of_mul_le_mul_right ?_ hstpos
    rw [hYmidmul, show (n : ℝ) * Real.sqrt t / 4 * Real.sqrt t = (n : ℝ) * t / 4 by
      rw [div_mul_eq_mul_div, mul_assoc, Real.mul_self_sqrt ht.le]]
    have hnt : (n : ℝ) * t / 4 ≤ (n : ℝ) * ChainDrift.horizon n / 4 := by
      have := mul_le_mul_of_nonneg_left htT hnpos.le; linarith
    refine le_trans hnt ?_
    rw [hsT, hT]
    have hlhs : (n : ℝ) * (16 * Real.log n / (n : ℝ) ^ 2) / 4 = 4 * Real.log n / (n : ℝ) := by
      field_simp; ring
    have hrhs : 2 * Real.log n * (4 * Real.sqrt (Real.log n) / (n : ℝ))
        = 8 * Real.log n * Real.sqrt (Real.log n) / (n : ℝ) := by ring
    rw [hlhs, hrhs, div_le_div_iff₀ hnpos hnpos]
    have h8 : (4 : ℝ) ≤ 8 * Real.sqrt (Real.log n) := by linarith [hsl3]
    have hLn : (0 : ℝ) ≤ Real.log n * (n : ℝ) := by positivity
    nlinarith [h8, hLn]
  have hjunk : Ymid * Real.sqrt t
      + ((n : ℝ) + 2) / 2 * (Ymid * Real.sqrt t) ^ 2 ≤ 3 := by
    rw [hYmidmul]
    exact junk_endpoint_two_log hn (le_of_eq hsT) hTpos.le
  have hJ2 : ∀ y ∈ Ioc (1 : ℝ) ((n : ℝ) * Real.sqrt t / 4),
      y * Real.sqrt t + ((n : ℝ) + 2) / 2 * (y * Real.sqrt t) ^ 2 ≤ 3 :=
    fun y hy => junk_le_of_endpoint hjunk (le_trans zero_le_one hy.1.le)
      (le_trans hy.2 hAY)
  have hJ3 : ∀ y ∈ Ioc ((n : ℝ) * Real.sqrt t / 4) Ymid,
      y * Real.sqrt t + ((n : ℝ) + 2) / 2 * (y * Real.sqrt t) ^ 2 ≤ 3 :=
    fun y hy => junk_le_of_endpoint hjunk (le_trans hA0 hy.1.le) hy.2
  have hct : ((n : ℝ) + 2) / 2 * t ≤ 1 / 100 := ct_le hn htT
  have hcs : ((n : ℝ) + 2) / 2 * Real.sqrt t ≤ 3 * Real.sqrt (Real.log n) := cs_le hn htT
  have hYmidL : 2 * Real.log n ≤ Ymid := by
    rw [hYmid, le_div_iff₀ hstpos]
    nlinarith [hst, hstpos, hL12, hsTpos]
  have hpYmid : (n : ℝ) * Real.sqrt t / 2 ≤ Ymid := by
    nlinarith [hAY, hnst, hstpos, hYmid0]
  have hnum := far_numerics hn hstpos hst2 hYmid0 hYmidL hpYmid hct hcs
  have hlam := hnum.1
  have hfar := hnum.2
  -- assemble
  have hpieces : ((n : ℝ) * Real.sqrt t / 2) *
      ∫ y in Ioc (0 : ℝ) Yt, Phi y * (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2))
      ≤ (Real.exp 6 + Real.exp 3 * (2 / Real.sqrt (2 * π) + 2) + 2 * Real.exp 3 + 1)
        * Real.exp ((n : ℝ) ^ 2 * t / 8) :=
    pieces_four (n := n) hn0 ht.le hst_half hA1 hAY hYmidhalf hb2
      (le_of_eq (by ring)) (le_of_eq (by ring)) hJ2 hJ3 hYmid0 hmidY1 hY1 hlam hfar
  have hchained : ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (y ^ (n - 1) * profile (a0C n) α W n t y)
      ≤ ENNReal.ofReal ((radiusOf (a0C n) α (Real.sqrt n / 2) t 0) ^ n / (2 * (n : ℝ))
        + Real.exp (1 / 2) / ((n : ℝ) * α ^ n)
          * (Real.exp 6 + Real.exp 3 * (2 / Real.sqrt (2 * π) + 2) + 2 * Real.exp 3 + 1)
          * Real.exp ((n : ℝ) ^ 2 * t / 8)) :=
    hgbound_chained hn0 hα ht ha1 hYt0 hW0 hdef hWdef2 hSc hlow hposw hWY hρ hρW
      (integrableOn_shell_lhs hα (by linarith) hY1 hWY hW0)
      (integrableOn_shell_rhs (α := α) hY1) hpieces
  have hnorm := hgbound_normalised hρ ht.le hchained
  rw [radiusOf_zero_eq] at hnorm
  unfold C1cR rhoC KcR Kc
  exact hnorm




/-- The reach window is nonnegative. -/
theorem windowR2_nonneg {α : ℝ} {n : ℕ} (hn : 2073600 ≤ n) (hα : 0 < α) :
    0 ≤ WindowR2.windowR2 α n := by
  rw [WindowR2.windowR2_eq]
  have h1 : 1 < WindowR2.reachNum2 n := WindowR2.one_lt_reachNum2 hn
  have h0 : (0 : ℝ) ≤ WindowR2.reachNum2 n := by linarith
  have hd : (0 : ℝ) ≤ WindowR2.reachNum2 n / α := div_nonneg h0 hα.le
  have hs : (0 : ℝ) ≤ Real.sqrt n / 2 := by positivity
  linarith

/-- **Lemma 4.3 at the reach window, uniformly in `t`.**  The `t ≥ t₀` branch is `hgbound_at2`;
below `t₀ = 16/n²` the profile's monotonicity in `t` reduces to the value at `t₀`, where
`e^{n²t₀/8} = e²`.  One constant `e²·C₁ᴿ` serves both.  The `n²` in the exponent is untouched. -/
theorem hgbound'_of_chain2 {α W : ℝ} {n : ℕ} (hn : 2073600 ≤ n) (hα : 0 < α)
    (hdef : (n : ℝ) * (α * Real.sqrt n / 2) ≤ 1 / 4)
    (hWdef : W = WindowR2.windowR2 α n) :
    ∀ t ∈ Ioc (0 : ℝ) (ChainDrift.horizon n),
      ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (y ^ (n - 1) * profile (a0C n) α W n t y)
        ≤ ENNReal.ofReal (Real.exp 2 * C1cR (a0C n) α n
            * Real.exp ((n : ℝ) ^ 2 / 8 * t)) := by
  intro t ht
  have hn0 : 0 < n := by omega
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hlog : (6 : ℝ) ≤ Real.log n := six_le_log hn
  have hC0 : 0 ≤ C1cR (a0C n) α n := C1cR_nonneg hα
  have he1 : (1 : ℝ) ≤ Real.exp ((n : ℝ) ^ 2 / 8 * t) :=
    Real.one_le_exp (mul_nonneg (by positivity) ht.1.le)
  have he2 : (1 : ℝ) ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
  have ht0T : 16 / (n : ℝ) ^ 2 ≤ ChainDrift.horizon n := by
    rw [horizon_eq, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  by_cases hbig : 16 / (n : ℝ) ^ 2 ≤ t
  · refine le_trans (hgbound_at2 hn hα hdef hWdef hbig ht.2) (ENNReal.ofReal_le_ofReal ?_)
    calc C1cR (a0C n) α n * Real.exp ((n : ℝ) ^ 2 * t / 8)
        = 1 * (C1cR (a0C n) α n * Real.exp ((n : ℝ) ^ 2 / 8 * t)) := by
          rw [show (n : ℝ) ^ 2 * t / 8 = (n : ℝ) ^ 2 / 8 * t by ring]; ring
      _ ≤ Real.exp 2 * (C1cR (a0C n) α n * Real.exp ((n : ℝ) ^ 2 / 8 * t)) := by gcongr
      _ = Real.exp 2 * C1cR (a0C n) α n * Real.exp ((n : ℝ) ^ 2 / 8 * t) := by ring
  · push Not at hbig
    have hmono : ∫⁻ y in Ioi (0 : ℝ),
          ENNReal.ofReal (y ^ (n - 1) * profile (a0C n) α W n t y)
        ≤ ∫⁻ y in Ioi (0 : ℝ),
            ENNReal.ofReal (y ^ (n - 1) * profile (a0C n) α W n (16 / (n : ℝ) ^ 2) y) := by
      refine lintegral_mono_ae ?_
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with y hy
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
        (profile_mono_time ht.1 hbig.le y) (pow_nonneg (le_of_lt hy) _))
    refine le_trans hmono (le_trans (hgbound_at2 hn hα hdef hWdef le_rfl ht0T)
      (ENNReal.ofReal_le_ofReal ?_))
    rw [show (n : ℝ) ^ 2 * (16 / (n : ℝ) ^ 2) / 8 = 2 by field_simp; norm_num]
    calc C1cR (a0C n) α n * Real.exp 2 = Real.exp 2 * C1cR (a0C n) α n * 1 := by ring
      _ ≤ Real.exp 2 * C1cR (a0C n) α n * Real.exp ((n : ℝ) ^ 2 / 8 * t) := by gcongr

/-! ## 9. Lemma 4.3's Bochner output at the reach window -/

/-- Lemma 4.3's radial profile at the reach window. -/
noncomputable def fR2 (α : ℝ) (n : ℕ) : ℝ → ℝ := fun r =>
  ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
    profile (a0C n) α (WindowR2.windowR2 α n) n t r

/-- Lemma 4.3's per-`t` constant at the reach window, with the small-`t` branch's `e²`. -/
theorem fR2_nonneg (α : ℝ) (n : ℕ) (r : ℝ) : 0 ≤ fR2 α n r :=
  setIntegral_nonneg measurableSet_Ioc (fun t _ => profile_nonneg t r)


/-- **Lemma 4.3 at the reach window, as `Params.radial_bound`.**  Tonelli over `(0,T]` turns the
uniform fixed-`t` bound into the radial bound, with `C = e²·C₁ᴿ·(8 − 8/n²)` — the `t`-integral
`∫₀ᵀ e^{n²t/8} dt = 8 − 8/n²` is exact, so the `n²` of the horizon cancels the `n⁻²` of the
exponent and the constant is absolute.  Kill rule 2 does not fire. -/
theorem radial_bound_of_chain2 {α W : ℝ} {n : ℕ} (hn : 2073600 ≤ n) (hα : 0 < α)
    (hdef : (n : ℝ) * (α * Real.sqrt n / 2) ≤ 1 / 4)
    (hWdef : W = WindowR2.windowR2 α n) :
    ∫ y in Ioi (0 : ℝ), y ^ (n - 1) *
        (∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n), profile (a0C n) α W n t y)
      ≤ Real.exp 2 * C1cR (a0C n) α n * (8 - 8 / (n : ℝ) ^ 2) := by
  have hn0 : 0 < n := by omega
  have hC0 : 0 ≤ Real.exp 2 * C1cR (a0C n) α n :=
    mul_nonneg (Real.exp_pos 2).le (C1cR_nonneg hα)
  have hT0 : (0 : ℝ) ≤ ChainDrift.horizon n := T_nonneg (by omega)
  have hW0 : 0 ≤ W := by rw [hWdef]; exact windowR2_nonneg hn hα
  have hgmeas : AEMeasurable
      (Function.uncurry (fun y t : ℝ =>
        ENNReal.ofReal (y ^ (n - 1) * profile (a0C n) α W n t y)))
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (volume.restrict (Ioc (0 : ℝ) (ChainDrift.horizon n)))) :=
    (((measurable_fst.pow_const (n - 1)).mul
      (measurable_profile_uncurry.comp measurable_swap)).ennreal_ofReal).aemeasurable
  refine radial_bound_of_lintegral
    (fun r => integral_nonneg_of_nonneg (fun t r => profile_nonneg t r) r)
    (mul_nonneg hC0 (eight_sub_nonneg hn0))
    (integrableOn_profile_radial_t hW0 hT0) ?_
  have hcongr : ∫⁻ y in Ioi (0 : ℝ),
        ENNReal.ofReal (y ^ (n - 1) *
          ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n), profile (a0C n) α W n t y)
      = ∫⁻ y in Ioi (0 : ℝ), ∫⁻ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
          ENNReal.ofReal (y ^ (n - 1) * profile (a0C n) α W n t y) :=
    setLIntegral_congr_fun measurableSet_Ioi (fun y hy =>
      (lintegral_t_ofReal (n := n) (le_of_lt hy) (fun t r => profile_nonneg t r)
        (integrableOn_profile_time y)).symm)
  rw [hcongr]
  exact lintegral_radial_t_le hn0 (horizon_eq n) hT0 hC0 _ hgmeas
    (hgbound'_of_chain2 hn hα hdef hWdef)

/-- **The radial bound in the `4·profile` shape brief 81's `params_of_raw2R_of_radial` consumes.**
The right-hand side is literally `TailAtStepR2.fR4 α n`, and `C = 4·C1R·(8 − 8/n²)`. -/
theorem radial_bound4_of_chain2 {α : ℝ} {n : ℕ} (hn : 2073600 ≤ n) (hα : 0 < α)
    (hdef : (n : ℝ) * (α * Real.sqrt n / 2) ≤ 1 / 4) :
    ∫ y in Ioi (0 : ℝ), y ^ (n - 1) *
        (4 * ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
          profile (a0C n) α (WindowR2.windowR2 α n) n t y)
      ≤ 4 * C1R α n * (8 - 8 / (n : ℝ) ^ 2) := by
  have h := radial_bound_of_chain2 (α := α) (W := WindowR2.windowR2 α n) hn hα hdef rfl
  have heq : ∀ y : ℝ, y ^ (n - 1) *
      (4 * ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
        profile (a0C n) α (WindowR2.windowR2 α n) n t y)
      = 4 * (y ^ (n - 1) * ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
        profile (a0C n) α (WindowR2.windowR2 α n) n t y) := by
    intro y; ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun y _ => heq y),
    MeasureTheory.integral_const_mul]
  have h4 := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 4)
  simp only [C1R]
  linarith

/-! ## 10b. The radial bound at the single time `t = T` (report 74 §4's terminal summand) -/

/-- **Lemma 4.3 at `t = T` alone, at the reach window.**  `e^{n²T/8} = e^{2·log n} = n²` exactly,
so the terminal summand's constant is `C₁ᴿ·n²`.  Report 74 §4's combined weight needs this. -/
theorem radial_bound_terminal2 {α : ℝ} {n : ℕ} (hn : 2073600 ≤ n) (hα : 0 < α)
    (hdef : (n : ℝ) * (α * Real.sqrt n / 2) ≤ 1 / 4) :
    ∫ y in Ioi (0 : ℝ), y ^ (n - 1) *
        profile (a0C n) α (WindowR2.windowR2 α n) n (ChainDrift.horizon n) y
      ≤ C1cR (a0C n) α n * (n : ℝ) ^ 2 := by
  have hn0 : 0 < n := by omega
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hlog : (6 : ℝ) ≤ Real.log n := six_le_log hn
  have hT : ChainDrift.horizon n = 16 * Real.log n / (n : ℝ) ^ 2 := horizon_eq n
  have ht0T : 16 / (n : ℝ) ^ 2 ≤ ChainDrift.horizon n := by
    rw [hT, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hexp : Real.exp ((n : ℝ) ^ 2 * ChainDrift.horizon n / 8) = (n : ℝ) ^ 2 := by
    rw [hT, show (n : ℝ) ^ 2 * (16 * Real.log n / (n : ℝ) ^ 2) / 8 = 2 * Real.log n by
      field_simp; ring]
    rw [show (2 : ℝ) * Real.log n = Real.log ((n : ℝ) ^ 2) by
      rw [Real.log_pow]; push_cast; ring]
    exact Real.exp_log (by positivity)
  have hC0 : 0 ≤ C1cR (a0C n) α n * (n : ℝ) ^ 2 :=
    mul_nonneg (C1cR_nonneg hα) (by positivity)
  have hW0 : (0 : ℝ) ≤ WindowR2.windowR2 α n := windowR2_nonneg hn hα
  refine radial_bound_of_lintegral (fun r => profile_nonneg _ r) hC0
    (integrableOn_profile_radial hW0 _) ?_
  have hle := hgbound_at2 (α := α) (W := WindowR2.windowR2 α n)
    (t := ChainDrift.horizon n) hn hα hdef rfl ht0T le_rfl
  rwa [hexp] at hle

/-! ## 11. The chain's input at the reach window, and `Params` -/

open Submission.L10.ChainDataInst Submission.L10.Tiling
open Submission.L10.Section5 Submission.L10.ConstructionA

/-- **The chain's input at the reach window.**  `Lemma43Uniform.ChainInput` with `windowC`
replaced by `WindowR2.windowR2` and `fC` by `fR`; nothing else moves. -/
structure ChainInputR2 (p n : ℕ) where
  alpha : ℝ
  alpha_pos : 0 < alpha
  alpha_norm : alpha ^ n * ((p ^ (n - 1) : ℕ) : ℝ) = kappa n
  R : ℝ
  R_nonneg : 0 ≤ R
  R_scaled : alpha * R ≤ 1 - 1 / (n : ℝ)
  R_lt_p : R < (p : ℝ)
  tiling_defect : (n : ℝ) * (alpha * Real.sqrt n / 2) ≤ 1 / 4
  window_lt_p : WindowR2.windowR2 alpha n < (p : ℝ)
  w : (Fin n → ℤ) → ℝ≥0∞
  supp : Finset (Fin n → ℤ)
  supp_ne_zero : ∀ y ∈ supp, y ≠ 0
  supp_radius : ∀ y ∈ supp, ‖toE n y‖ ≤ WindowR2.windowR2 alpha n
  dom : ∀ y ∈ supp, ∀ x ∈ cube (toE n y), w y ≤ ENNReal.ofReal (fR2 alpha n ‖x‖)
  arith : (n : ℝ) * kappa n * ((p : ℝ) - 1) * (8 - 8 / (n : ℝ) ^ 2) < 8 * ((p : ℝ) ^ n - 1)

/-- **`Params` at the reach window**, every field supplied — the record filled exactly as
`TailAtStep.params_of_raw2` fills it, with `windowC → WindowR2.windowR2`, `fC → fR`,
`C1C → C1R`. -/
noncomputable def params_of_chainR2 {p n : ℕ} [Fact (Nat.Prime p)] (hn : 2073600 ≤ n)
    (I : ChainInputR2 p n) : Params p n where
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
  windowRadius := WindowR2.windowR2 I.alpha n
  window_lt_p := I.window_lt_p
  f := fR2 I.alpha n
  f_nonneg := fR2_nonneg I.alpha n
  w := I.w
  supp := I.supp
  supp_ne_zero := I.supp_ne_zero
  supp_radius := I.supp_radius
  dom := I.dom
  integrable := integrable_radial_euclidean (a₀ := a0C n) (α := I.alpha)
    (W := WindowR2.windowR2 I.alpha n) (T := ChainDrift.horizon n) (n := n)
    (T_nonneg (by omega : 1 ≤ n))
  C := C1R I.alpha n * (8 - 8 / (n : ℝ) ^ 2)
  radial_bound := radial_bound_of_chain2 hn I.alpha_pos I.tiling_defect rfl
  theta := ENNReal.ofReal (16 * C1R I.alpha n)
  theta_ne_zero := by
    have := C1R_pos (α := I.alpha) (n := n) (by omega) I.alpha_pos
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    linarith
  theta_ne_top := ENNReal.ofReal_ne_top
  markov :=
    markov_of_arith (by omega) (Nat.Prime.one_lt (Fact.out)).le
      (Nat.one_lt_pow (by omega) (Nat.Prime.one_lt (Fact.out)))
      (C1R_pos (α := I.alpha) (n := n) (by omega) I.alpha_pos) I.arith

/-- `ChainData` at the reach window. -/
noncomputable def chainData_of_chainR2 {p n : ℕ} [Fact (Nat.Prime p)] [NeZero p]
    (hn : 2073600 ≤ n) (I : ChainInputR2 p n) : ChainData p n :=
  chainData_of_params (params_of_chainR2 hn I)

/-- §5's line `g`, at the reach window. -/
theorem exists_good_line_of_chainR2 {p n : ℕ} [Fact (Nat.Prime p)] [NeZero p]
    (hn : 2073600 ≤ n) (I : ChainInputR2 p n) :
    ∃ g : Fin n → ZMod p, g ≠ 0 ∧
      (∀ y : Fin n → ℤ, y ≠ 0 → ‖toE n y‖ ≤ I.R → y ∉ latZ p n g) ∧
      ∑ y ∈ I.supp.filter (fun y => y ∈ latZ p n g), I.w y
        < ENNReal.ofReal (16 * C1R I.alpha n) :=
  exists_good_line_of_params (params_of_chainR2 hn I)

end Submission.L10.Lemma43R2

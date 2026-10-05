/-
Gate L-10 (`klartag_packing`), brief 71.

**Lemma 4.3 at the reach window.**

The near piece runs to `2·log n` (report 70's split point) and the far band from there to `YR`.
`HJ.junk_endpoint_le_three`'s `20·(log n)³/n ≤ 3` route is 100× loose at `n₁` because
`HJ.log_cube_le` (`L³ ≤ 216√n`) is; at the doubled endpoint the junk is four times as large in its
quadratic term, so a sharper log bound is needed.  `log n ≤ 16·n^{1/16}` — four nested square
roots, no `rpow` — gives `L³/n ≤ 4096·n^{−13/16} = 0.0302` at `n₁` against a budget of `0.075`.
-/
import Submission.L10.FarBand
import Submission.L10.Lemma43Uniform

namespace Submission.L10.Lemma43R

open MeasureTheory Set Real Submission.L10
open scoped ENNReal NNReal

/-! ## 1. A sharper logarithm bound: `log n ≤ 16·n^{1/16}` -/

/-- `n^{1/16}`, as four nested square roots. -/
noncomputable def r16 (n : ℕ) : ℝ := Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt (n : ℝ))))

theorem r16_pos {n : ℕ} (hn : 0 < (n : ℝ)) : 0 < r16 n :=
  Real.sqrt_pos.2 (Real.sqrt_pos.2 (Real.sqrt_pos.2 (Real.sqrt_pos.2 hn)))

theorem r16_pow {n : ℕ} (hn : 0 ≤ (n : ℝ)) : r16 n ^ 16 = (n : ℝ) := by
  have h1 : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hn
  have h2 : Real.sqrt (Real.sqrt (n : ℝ)) ^ 2 = Real.sqrt (n : ℝ) :=
    Real.sq_sqrt (Real.sqrt_nonneg _)
  have h3 : Real.sqrt (Real.sqrt (Real.sqrt (n : ℝ))) ^ 2 = Real.sqrt (Real.sqrt (n : ℝ)) :=
    Real.sq_sqrt (Real.sqrt_nonneg _)
  have h4 : r16 n ^ 2 = Real.sqrt (Real.sqrt (Real.sqrt (n : ℝ))) :=
    Real.sq_sqrt (Real.sqrt_nonneg _)
  calc r16 n ^ 16 = ((((r16 n ^ 2) ^ 2) ^ 2) ^ 2) := by ring
    _ = (n : ℝ) := by rw [h4, h3, h2, h1]

theorem log_le_r16 {n : ℕ} (hn : 2073600 ≤ n) : Real.log n ≤ 16 * r16 n := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have h1 : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
  have h2 : (0 : ℝ) < Real.sqrt (Real.sqrt (n : ℝ)) := Real.sqrt_pos.2 h1
  have h3 : (0 : ℝ) < Real.sqrt (Real.sqrt (Real.sqrt (n : ℝ))) := Real.sqrt_pos.2 h2
  have h4 : (0 : ℝ) < r16 n := r16_pos hn0
  have hlog : Real.log (r16 n) = Real.log n / 16 := by
    rw [r16, Real.log_sqrt h3.le, Real.log_sqrt h2.le, Real.log_sqrt h1.le,
      Real.log_sqrt hn0.le]
    ring
  have hle := Real.log_le_sub_one_of_pos h4
  rw [hlog] at hle
  linarith

theorem r16_ge {n : ℕ} (hn : 2073600 ≤ n) : (2.4 : ℝ) ≤ r16 n := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have h4 : (0 : ℝ) < r16 n := r16_pos hn0
  have hpow : r16 n ^ 16 = (n : ℝ) := r16_pow hn0.le
  by_contra hcon
  push Not at hcon
  have hlt : r16 n ^ 16 ≤ (2.4 : ℝ) ^ 16 := pow_le_pow_left₀ h4.le hcon.le 16
  rw [hpow] at hlt
  norm_num at hlt
  linarith

/-! ## 2. The junk endpoint at `2·log n` -/

/-- **The twin of `HJ.junk_endpoint_le_three` at the doubled endpoint.**  `0.0477` against `3` at
`n₁`; the proof budget is `41·(log n)³/n ≤ 3`, i.e. `(log n)³/n ≤ 0.0731`, against an actual
`0.0302` from `log n ≤ 16·n^{1/16}`. -/
theorem junk_endpoint_two_log {n : ℕ} (hn : 2073600 ≤ n) {t : ℝ}
    (hts : Real.sqrt t ≤ 4 * Real.sqrt (Real.log n) / (n : ℝ)) (ht : 0 ≤ t) :
    2 * Real.log n * Real.sqrt t
      + ((n : ℝ) + 2) / 2 * (2 * Real.log n * Real.sqrt t) ^ 2 ≤ 3 := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hL : (6 : ℝ) ≤ Real.log n := six_le_log hn
  have hL1 : (1 : ℝ) ≤ Real.log n := by linarith
  have hsL : (0 : ℝ) ≤ Real.sqrt (Real.log n) := Real.sqrt_nonneg _
  have hsL2 : Real.sqrt (Real.log n) ^ 2 = Real.log n := Real.sq_sqrt (by linarith)
  have hst : (0 : ℝ) ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hst2 : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht
  -- the two terms against `L³/n`
  have hsLle : Real.sqrt (Real.log n) ≤ Real.log n := by nlinarith [hsL, hsL2, hL1]
  have hlin : 2 * Real.log n * Real.sqrt t ≤ 8 * Real.log n ^ 3 / (n : ℝ) := by
    have h1 : Real.sqrt t ≤ 4 * Real.log n / (n : ℝ) := by
      refine le_trans hts ?_
      rw [div_le_div_iff₀ hn0 hn0]; nlinarith [hsLle, hn0]
    have h2 : 2 * Real.log n * Real.sqrt t ≤ 2 * Real.log n * (4 * Real.log n / (n : ℝ)) :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    refine le_trans h2 ?_
    rw [show 2 * Real.log n * (4 * Real.log n / (n : ℝ)) = 8 * Real.log n ^ 2 / (n : ℝ) by ring,
      div_le_div_iff₀ hn0 hn0]
    have hL23 : Real.log n ^ 2 ≤ Real.log n ^ 3 := by nlinarith [hL1]
    nlinarith [hL23, hn0]
  have htle : t ≤ 16 * Real.log n / (n : ℝ) ^ 2 := by
    have h1 : Real.sqrt t ^ 2 ≤ (4 * Real.sqrt (Real.log n) / (n : ℝ)) ^ 2 :=
      pow_le_pow_left₀ hst hts 2
    rw [hst2, div_pow, mul_pow, hsL2] at h1
    calc t ≤ 4 ^ 2 * Real.log n / (n : ℝ) ^ 2 := h1
      _ = 16 * Real.log n / (n : ℝ) ^ 2 := by norm_num
  have hquad : ((n : ℝ) + 2) / 2 * (2 * Real.log n * Real.sqrt t) ^ 2
      ≤ 33 * Real.log n ^ 3 / (n : ℝ) := by
    have hexp : (2 * Real.log n * Real.sqrt t) ^ 2 = 4 * Real.log n ^ 2 * t := by
      rw [mul_pow, mul_pow, hst2]; ring
    rw [hexp]
    have hb : 4 * Real.log n ^ 2 * t ≤ 4 * Real.log n ^ 2 * (16 * Real.log n / (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left htle (by positivity)
    have hfac : ((n : ℝ) + 2) / 2 * (4 * Real.log n ^ 2 * (16 * Real.log n / (n : ℝ) ^ 2))
        = 32 * ((n : ℝ) + 2) * Real.log n ^ 3 / (n : ℝ) ^ 2 := by field_simp; ring
    calc ((n : ℝ) + 2) / 2 * (4 * Real.log n ^ 2 * t)
        ≤ ((n : ℝ) + 2) / 2 * (4 * Real.log n ^ 2 * (16 * Real.log n / (n : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = 32 * ((n : ℝ) + 2) * Real.log n ^ 3 / (n : ℝ) ^ 2 := hfac
      _ ≤ 33 * Real.log n ^ 3 / (n : ℝ) := by
          rw [div_le_div_iff₀ (by positivity) hn0]
          have hkey : 0 ≤ (33 * (n : ℝ) - 32 * ((n : ℝ) + 2)) * (Real.log n ^ 3 * (n : ℝ)) :=
            mul_nonneg (by linarith) (by positivity)
          nlinarith [hkey]
  -- `41·L³/n ≤ 3`
  have hcube : Real.log n ^ 3 ≤ 4096 * r16 n ^ 3 := by
    have h := log_le_r16 hn
    have h0 : (0 : ℝ) ≤ Real.log n := by linarith
    calc Real.log n ^ 3 ≤ (16 * r16 n) ^ 3 := pow_le_pow_left₀ h0 h 3
      _ = 4096 * r16 n ^ 3 := by ring
  have hpow : r16 n ^ 16 = (n : ℝ) := r16_pow hn0.le
  have hr : (2.4 : ℝ) ≤ r16 n := r16_ge hn
  have hr0 : (0 : ℝ) < r16 n := r16_pos hn0
  have h13 : (2.4 : ℝ) ^ 13 ≤ r16 n ^ 13 := pow_le_pow_left₀ (by norm_num) hr 13
  have hn16 : r16 n ^ 13 * r16 n ^ 3 = (n : ℝ) := by rw [← hpow]; ring
  have hstep : 41 * Real.log n ^ 3 ≤ 167936 * r16 n ^ 3 := by nlinarith [hcube]
  have h24 : (87000 : ℝ) ≤ r16 n ^ 13 := le_trans (by norm_num) h13
  have hfin : 41 * (Real.log n ^ 3 / (n : ℝ)) ≤ 3 := by
    rw [mul_div_assoc'] at *
    rw [div_le_iff₀ hn0]
    calc 41 * Real.log n ^ 3 ≤ 167936 * r16 n ^ 3 := hstep
      _ ≤ 3 * (r16 n ^ 13 * r16 n ^ 3) := by nlinarith [h24, pow_pos hr0 3]
      _ = 3 * (n : ℝ) := by rw [hn16]
  have hlin' : 2 * Real.log n * Real.sqrt t ≤ 8 * (Real.log n ^ 3 / (n : ℝ)) := by
    rw [mul_div_assoc'] at *; linarith [hlin]
  have hquad' : ((n : ℝ) + 2) / 2 * (2 * Real.log n * Real.sqrt t) ^ 2
      ≤ 33 * (Real.log n ^ 3 / (n : ℝ)) := by
    rw [mul_div_assoc'] at *; linarith [hquad]
  linarith [hlin', hquad', hfin]

/-! ## 3. The four-piece bound -/

/-- **The four-piece radial bound.**  `pieces_at_params` on `(0, Ymid]` and `FarBand.far_le` on
`(Ymid, Y1]`, summed.  The far band contributes at most `1`, so `K` becomes `K + 1`. -/
theorem pieces_four {t A Ymid Y1 : ℝ} {n : ℕ} (hn : 0 < n) (ht : 0 ≤ t)
    (hts : Real.sqrt t ≤ 1 / 2) (hA1 : 1 ≤ A) (hAY : A ≤ Ymid)
    (hY : Ymid * Real.sqrt t ≤ 1 / 2)
    (hb2 : 2 ≤ (n : ℝ) * Real.sqrt t / 2)
    (hLb : (n : ℝ) * Real.sqrt t / 2 / 2 ≤ A)
    (hbA : (n : ℝ) * Real.sqrt t / 2 ≤ 2 * A)
    (hJ2 : ∀ y ∈ Ioc (1 : ℝ) A,
      y * Real.sqrt t + ((n : ℝ) + 2) / 2 * (y * Real.sqrt t) ^ 2 ≤ 3)
    (hJ3 : ∀ y ∈ Ioc A Ymid,
      y * Real.sqrt t + ((n : ℝ) + 2) / 2 * (y * Real.sqrt t) ^ 2 ≤ 3)
    (hmid0 : 0 < Ymid) (hmidY1 : Ymid ≤ Y1) (hY1 : Y1 * Real.sqrt t ≤ 1 / 2)
    (hlam : 0 < 2 * (1 / 2 - ((n : ℝ) + 2) / 2 * Real.sqrt t ^ 2) * Ymid
      - ((n : ℝ) + 2) / 2 * Real.sqrt t)
    (hfar : (n : ℝ) * Real.sqrt t / 2
      * (Real.exp (((n : ℝ) + 2) / 2 * Real.sqrt t * Ymid
          - (1 / 2 - ((n : ℝ) + 2) / 2 * Real.sqrt t ^ 2) * Ymid ^ 2)
        / ((2 * (1 / 2 - ((n : ℝ) + 2) / 2 * Real.sqrt t ^ 2) * Ymid
            - ((n : ℝ) + 2) / 2 * Real.sqrt t) * (Real.sqrt (2 * π) * Ymid))) ≤ 1) :
    ((n : ℝ) * Real.sqrt t / 2) *
        ∫ y in Ioc (0 : ℝ) Y1, Phi y * (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2))
      ≤ (Real.exp 6 + Real.exp 3 * (2 / Real.sqrt (2 * π) + 2) + 2 * Real.exp 3 + 1)
        * Real.exp ((n : ℝ) ^ 2 * t / 8) := by
  have hst : (0 : ℝ) ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hp0 : (0 : ℝ) ≤ (n : ℝ) * Real.sqrt t / 2 := by positivity
  have hc0 : (0 : ℝ) ≤ ((n : ℝ) + 2) / 2 := by positivity
  have hint1 : IntegrableOn
      (fun y : ℝ => Phi y * (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2)))
      (Ioc (0 : ℝ) Ymid) := integrableOn_pieces (n := n) le_rfl hY
  have hint2 : IntegrableOn
      (fun y : ℝ => Phi y * (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2)))
      (Ioc Ymid Y1) := integrableOn_pieces (n := n) hmid0.le hY1
  have hint0 : IntegrableOn
      (fun y : ℝ => Phi y * (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2)))
      (Ioc (0 : ℝ) (0 : ℝ)) := by simp
  have hsplit := setIntegral_Ioc_split₃ (f := fun y : ℝ =>
      Phi y * (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2)))
    (le_refl (0 : ℝ)) hmid0.le hmidY1 hint0 hint1 hint2
  have hzero : ∫ y in Ioc (0 : ℝ) (0 : ℝ),
      Phi y * (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2)) = 0 := by simp
  rw [hzero, zero_add] at hsplit
  have hnear := pieces_at_params (n := n) hn ht hts hA1 hAY hY hb2 hLb hbA hJ2 hJ3
  have hfarb := FarBand.far_le (s := Real.sqrt t) (c := ((n : ℝ) + 2) / 2) (Y₀ := Ymid)
    (Y₁ := Y1) (p := (n : ℝ) * Real.sqrt t / 2) hst hc0 hmid0 hp0 hY1 hlam hint2
  have hexp1 : (1 : ℝ) ≤ Real.exp ((n : ℝ) ^ 2 * t / 8) := Real.one_le_exp (by positivity)
  rw [hsplit, mul_add]
  have hfar2 : (n : ℝ) * Real.sqrt t / 2
      * ∫ y in Ioc Ymid Y1, Phi y * (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2))
      ≤ 1 * Real.exp ((n : ℝ) ^ 2 * t / 8) := by
    refine le_trans (le_trans hfarb hfar) ?_
    linarith
  linarith [hnear, hfar2]

/-! ## 4. The numeric facts at the reach endpoint -/

/-- `log n·√T ≤ 1/4` — the quarter version of `Lemma43Uniform.logn_sqrtT_le`, needed because the
split point is `2·log n`. -/
theorem logn_sqrtT_le_quarter {n : ℕ} (hn : 2073600 ≤ n) :
    Real.log n * Real.sqrt (ChainDrift.horizon n) ≤ 1 / 4 := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hlog : (1 : ℝ) ≤ Real.log n := by linarith [six_le_log hn]
  have hTnn : (0 : ℝ) ≤ ChainDrift.horizon n := (horizon_pos (by omega)).le
  have hcube : (Real.log n) ^ 3 ≤ 216 * Real.sqrt n := log_cube_le (by omega)
  have hsn : (1440 : ℝ) ≤ Real.sqrt n := by
    rw [show (1440 : ℝ) = Real.sqrt (1440 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num; linarith)
  have hsq : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt hn0.le
  have h256 : 256 * (Real.log n) ^ 3 ≤ (n : ℝ) ^ 2 := by nlinarith [hcube, hsn, hsq]
  have hsqeq : (Real.log n * Real.sqrt (ChainDrift.horizon n)) ^ 2
      = 16 * (Real.log n) ^ 3 / (n : ℝ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hTnn, horizon_eq]; ring
  have hkey : (Real.log n * Real.sqrt (ChainDrift.horizon n)) ^ 2 ≤ 1 / 16 := by
    rw [hsqeq, div_le_iff₀ (by positivity)]; linarith
  have hx0 : 0 ≤ Real.log n * Real.sqrt (ChainDrift.horizon n) :=
    mul_nonneg (by linarith) (Real.sqrt_nonneg _)
  nlinarith [hkey, hx0]

/-- `2·log n·√T ≤ a0C n − mR n` — the split point is inside the reach window. -/
theorem two_logn_sqrtT_le_gap {n : ℕ} (hn : 2073600 ≤ n) :
    2 * Real.log n * Real.sqrt (ChainDrift.horizon n) ≤ a0C n - WindowR.mR n := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hlog : (1 : ℝ) ≤ Real.log n := by linarith [six_le_log hn]
  have hTnn : (0 : ℝ) ≤ ChainDrift.horizon n := (horizon_pos (by omega)).le
  have hqrt : Real.log n ≤ 4 * Real.sqrt (Real.sqrt (n : ℝ)) := WindowR.log_le_four_qrt hn
  have hq4 : Real.sqrt (Real.sqrt (n : ℝ)) ^ 4 = (n : ℝ) := WindowR.qrt_pow_four hn0.le
  have hq37 : (37 : ℝ) ≤ Real.sqrt (Real.sqrt (n : ℝ)) := WindowR.qrt_ge hn
  have hq0 : (0 : ℝ) < Real.sqrt (Real.sqrt (n : ℝ)) := by linarith
  have hL2 : Real.log n ^ 2 ≤ 9 * (n : ℝ) := by
    have h16 : Real.log n ^ 2 ≤ 16 * Real.sqrt (Real.sqrt (n : ℝ)) ^ 2 := by
      nlinarith [hqrt, hlog, hq0]
    nlinarith [h16, hq4, hq37, hq0]
  -- `(2L√T)² ≤ r₀²`
  have hsq2 : DriftStopped6.r0Adopted n ^ 2 = 576 * (Real.log n / (n : ℝ)) :=
    WindowR.r0Adopted_sq (by omega)
  have hlhs : (2 * Real.log n * Real.sqrt (ChainDrift.horizon n)) ^ 2
      = 64 * Real.log n ^ 3 / (n : ℝ) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hTnn, horizon_eq]; ring
  have hcmp : (2 * Real.log n * Real.sqrt (ChainDrift.horizon n)) ^ 2
      ≤ DriftStopped6.r0Adopted n ^ 2 := by
    rw [hlhs, hsq2,
      show (576 : ℝ) * (Real.log n / (n : ℝ)) = 576 * Real.log n / (n : ℝ) by ring,
      div_le_div_iff₀ (by positivity) hn0]
    have hkey : 0 ≤ (576 * (n : ℝ) - 64 * Real.log n ^ 2) * (Real.log n * (n : ℝ)) :=
      mul_nonneg (by linarith) (by positivity)
    nlinarith [hkey]
  have hx0 : 0 ≤ 2 * Real.log n * Real.sqrt (ChainDrift.horizon n) := by positivity
  have hr0 : 2 * Real.log n * Real.sqrt (ChainDrift.horizon n) ≤ DriftStopped6.r0Adopted n := by
    nlinarith [hcmp, hx0, WindowR.r0Adopted_nonneg n]
  have hgap : a0C n - WindowR.mR n = DriftStopped6.r0Adopted n
      + DriftStopped6.c3Adopted n * DriftStopped6.etaAdopted n := by rw [WindowR.mR_eq]; ring
  have hηnn : 0 ≤ DriftStopped6.c3Adopted n * DriftStopped6.etaAdopted n := by
    rw [DriftStopped6.c3Adopted, DriftStopped6.etaAdopted]; positivity
  rw [hgap]; linarith

/-- `12 ≤ log n` at the threshold (`e¹² = 162 755 ≤ 2 073 600`). -/
theorem twelve_le_log {n : ℕ} (hn : 2073600 ≤ n) : (12 : ℝ) ≤ Real.log n := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  rw [Real.le_log_iff_exp_le hn0]
  have h12 : Real.exp 12 = Real.exp 1 ^ (12 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
  have he : Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
  calc Real.exp 12 = Real.exp 1 ^ (12 : ℕ) := h12
    _ ≤ (2.7182818286 : ℝ) ^ (12 : ℕ) := pow_le_pow_left₀ (Real.exp_pos 1).le he 12
    _ ≤ 2073600 := by norm_num
    _ ≤ (n : ℝ) := hnR

/-! ## 5. Lemma 4.3's constant at the reach window -/

/-- `pieces_four`'s constant: `Lemma43Uniform.Kc + 1`. -/
noncomputable def KcR : ℝ := Kc + 1

/-- Lemma 4.3's per-`t` constant at the reach window. -/
noncomputable def C1cR (a₀ α : ℝ) (n : ℕ) : ℝ :=
  rhoC a₀ α n ^ n / (2 * (n : ℝ)) + Real.exp (1 / 2) / ((n : ℝ) * α ^ n) * KcR

theorem KcR_nonneg : 0 ≤ KcR := by unfold KcR Kc; positivity

theorem C1cR_nonneg {a₀ α : ℝ} {n : ℕ} (hα : 0 < α) : 0 ≤ C1cR a₀ α n := by
  have hr : 0 ≤ rhoC a₀ α n := rhoC_nonneg hα
  refine add_nonneg (div_nonneg (pow_nonneg hr _) (by positivity)) ?_
  exact mul_nonneg (by positivity) KcR_nonneg

theorem C1cR_pos {a₀ α : ℝ} {n : ℕ} (hn : 0 < n) (hα : 0 < α) (ha₀ : 0 < a₀) :
    0 < C1cR a₀ α n := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hr : 0 < rhoC a₀ α n := by
    unfold rhoC
    have : (0 : ℝ) < (Real.sqrt a₀)⁻¹ / α := by positivity
    positivity
  have h1 : 0 < rhoC a₀ α n ^ n / (2 * (n : ℝ)) := by positivity
  have h2 : 0 ≤ Real.exp (1 / 2) / ((n : ℝ) * α ^ n) * KcR :=
    mul_nonneg (by positivity) KcR_nonneg
  unfold C1cR; linarith

/-- `((n+2)/2)·t ≤ 1/100` for `t ≤ T` — the far band's `a ≥ 0.49`. -/
theorem ct_le {n : ℕ} (hn : 2073600 ≤ n) {t : ℝ} (htT : t ≤ ChainDrift.horizon n) :
    ((n : ℝ) + 2) / 2 * t ≤ 1 / 100 := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hL : (6 : ℝ) ≤ Real.log n := six_le_log hn
  have hlm : 9216 * Real.log n ≤ (n : ℝ) := WindowR.log_mul_le hn
  have h2 : ((n : ℝ) + 2) / 2 * t ≤ ((n : ℝ) + 2) / 2 * ChainDrift.horizon n :=
    mul_le_mul_of_nonneg_left htT (by positivity)
  refine le_trans h2 ?_
  rw [horizon_eq,
    show ((n : ℝ) + 2) / 2 * (16 * Real.log n / (n : ℝ) ^ 2)
      = 8 * ((n : ℝ) + 2) * Real.log n / (n : ℝ) ^ 2 by ring,
    div_le_div_iff₀ (by positivity) (by norm_num)]
  have hLn : Real.log n ≤ Real.log n * (n : ℝ) := by nlinarith [hL, hn0]
  have hmul : 9216 * Real.log n * (n : ℝ) ≤ (n : ℝ) * (n : ℝ) :=
    mul_le_mul_of_nonneg_right hlm hn0.le
  nlinarith [hmul, hLn, hL, hn0]

/-- `((n+2)/2)·√t ≤ 3·√(log n)` for `t ≤ T`. -/
theorem cs_le {n : ℕ} (hn : 2073600 ≤ n) {t : ℝ} (htT : t ≤ ChainDrift.horizon n) :
    ((n : ℝ) + 2) / 2 * Real.sqrt t ≤ 3 * Real.sqrt (Real.log n) := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hL : (6 : ℝ) ≤ Real.log n := six_le_log hn
  have hslpos : (0 : ℝ) < Real.sqrt (Real.log n) := Real.sqrt_pos.2 (by linarith)
  have hsT : Real.sqrt (ChainDrift.horizon n) = 4 * Real.sqrt (Real.log n) / (n : ℝ) :=
    sqrtT_eq (by omega) (horizon_eq n)
  have h1 : Real.sqrt t ≤ Real.sqrt (ChainDrift.horizon n) := Real.sqrt_le_sqrt htT
  have h2 : ((n : ℝ) + 2) / 2 * Real.sqrt t
      ≤ ((n : ℝ) + 2) / 2 * Real.sqrt (ChainDrift.horizon n) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  refine le_trans h2 ?_
  rw [hsT, show ((n : ℝ) + 2) / 2 * (4 * Real.sqrt (Real.log n) / (n : ℝ))
    = 2 * ((n : ℝ) + 2) * Real.sqrt (Real.log n) / (n : ℝ) by ring,
    div_le_iff₀ hn0]
  nlinarith [hslpos, hn0, hnR]

/-- **The far band's two numeric side conditions**, as a standalone lemma: `pieces_four`'s `hlam`
and `hfar` at the split point `Ymid ≥ 2·log n`. -/
theorem far_numerics {t Ymid : ℝ} {n : ℕ} (hn : 2073600 ≤ n)
    (hstpos : 0 < Real.sqrt t) (hst2 : Real.sqrt t ^ 2 = t)
    (hYmid0 : 0 < Ymid) (hYmidL : 2 * Real.log n ≤ Ymid)
    (hpYmid : (n : ℝ) * Real.sqrt t / 2 ≤ Ymid)
    (hct : ((n : ℝ) + 2) / 2 * t ≤ 1 / 100)
    (hcs : ((n : ℝ) + 2) / 2 * Real.sqrt t ≤ 3 * Real.sqrt (Real.log n)) :
    (0 < 2 * (1 / 2 - ((n : ℝ) + 2) / 2 * Real.sqrt t ^ 2) * Ymid
        - ((n : ℝ) + 2) / 2 * Real.sqrt t)
      ∧ (n : ℝ) * Real.sqrt t / 2
        * (Real.exp (((n : ℝ) + 2) / 2 * Real.sqrt t * Ymid
            - (1 / 2 - ((n : ℝ) + 2) / 2 * Real.sqrt t ^ 2) * Ymid ^ 2)
          / ((2 * (1 / 2 - ((n : ℝ) + 2) / 2 * Real.sqrt t ^ 2) * Ymid
              - ((n : ℝ) + 2) / 2 * Real.sqrt t) * (Real.sqrt (2 * π) * Ymid))) ≤ 1 := by
  have hL12 : (12 : ℝ) ≤ Real.log n := twelve_le_log hn
  have hsl2 : Real.sqrt (Real.log n) ^ 2 = Real.log n := Real.sq_sqrt (by linarith)
  have hslpos : (0 : ℝ) < Real.sqrt (Real.log n) := Real.sqrt_pos.2 (by linarith)
  have hsl346 : (3.46 : ℝ) ≤ Real.sqrt (Real.log n) := by
    rw [show (3.46 : ℝ) = Real.sqrt (3.46 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num; linarith)
  set aq : ℝ := 1 / 2 - ((n : ℝ) + 2) / 2 * Real.sqrt t ^ 2 with haqdef
  have haq : (49 : ℝ) / 100 ≤ aq := by rw [haqdef, hst2]; linarith
  have h3sl : 3 * Real.sqrt (Real.log n) ≤ 98 / 100 * Real.log n := by
    nlinarith [hsl2, hsl346, hslpos]
  have hcs098 : ((n : ℝ) + 2) / 2 * Real.sqrt t ≤ 98 / 100 * Real.log n := le_trans hcs h3sl
  have hcsL : ((n : ℝ) + 2) / 2 * Real.sqrt t ≤ Real.log n := by linarith
  have haqY : 98 / 100 * Real.log n ≤ aq * Ymid := by
    have h1 : (49 : ℝ) / 100 * (2 * Real.log n) ≤ aq * Ymid :=
      mul_le_mul haq hYmidL (by linarith) (by linarith)
    linarith
  have hlam : (11 : ℝ) ≤ 2 * aq * Ymid - ((n : ℝ) + 2) / 2 * Real.sqrt t := by
    linarith [haqY, hcsL, hL12]
  have hkey : ((n : ℝ) + 2) / 2 * Real.sqrt t ≤ aq * Ymid := le_trans hcs098 haqY
  have hC0 : ((n : ℝ) + 2) / 2 * Real.sqrt t * Ymid - aq * Ymid ^ 2 ≤ 0 := by
    have h := mul_le_mul_of_nonneg_right hkey hYmid0.le
    nlinarith [h]
  have hpi2 : (2 : ℝ) ≤ Real.sqrt (2 * π) := by
    have h4 : (4 : ℝ) ≤ 2 * π := by nlinarith [Real.pi_gt_three]
    have h5 := Real.sqrt_le_sqrt h4
    rwa [show Real.sqrt 4 = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h5
  refine ⟨by linarith, ?_⟩
  have hexp1 : Real.exp (((n : ℝ) + 2) / 2 * Real.sqrt t * Ymid - aq * Ymid ^ 2) ≤ 1 := by
    rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero]]
    exact Real.exp_le_exp.2 hC0
  have hprod11 : (11 : ℝ) * 2
      ≤ (2 * aq * Ymid - ((n : ℝ) + 2) / 2 * Real.sqrt t) * Real.sqrt (2 * π) :=
    mul_le_mul hlam hpi2 (by norm_num) (by linarith)
  have hden : (22 : ℝ) * Ymid
      ≤ (2 * aq * Ymid - ((n : ℝ) + 2) / 2 * Real.sqrt t) * (Real.sqrt (2 * π) * Ymid) := by
    calc (22 : ℝ) * Ymid = (11 * 2) * Ymid := by ring
      _ ≤ ((2 * aq * Ymid - ((n : ℝ) + 2) / 2 * Real.sqrt t) * Real.sqrt (2 * π)) * Ymid :=
          mul_le_mul_of_nonneg_right hprod11 hYmid0.le
      _ = (2 * aq * Ymid - ((n : ℝ) + 2) / 2 * Real.sqrt t) * (Real.sqrt (2 * π) * Ymid) := by
          ring
  have hnum : (0 : ℝ) < (2 * aq * Ymid - ((n : ℝ) + 2) / 2 * Real.sqrt t)
      * (Real.sqrt (2 * π) * Ymid) := by linarith [hden, hYmid0]
  rw [mul_div_assoc', div_le_one hnum]
  have hp0 : (0 : ℝ) ≤ (n : ℝ) * Real.sqrt t / 2 := by positivity
  have hprod : (n : ℝ) * Real.sqrt t / 2
      * Real.exp (((n : ℝ) + 2) / 2 * Real.sqrt t * Ymid - aq * Ymid ^ 2) ≤ Ymid := by
    nlinarith [hexp1, hpYmid, hp0, Real.exp_pos (((n : ℝ) + 2) / 2 * Real.sqrt t * Ymid
      - aq * Ymid ^ 2)]
  linarith [hprod, hden, hYmid0]

set_option maxHeartbeats 1000000 in
/-- **Lemma 4.3 at a single `t ≥ 16/n²`, at the reach window.** -/
theorem hgbound_at' {α W t : ℝ} {n : ℕ} (hn : 2073600 ≤ n) (hα : 0 < α)
    (hdef : (n : ℝ) * (α * Real.sqrt n / 2) ≤ 1 / 4)
    (hWdef : W = WindowR.windowR α n)
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
  have hmRpos : 0 < WindowR.mR n := WindowR.mR_pos hn
  have hgap : Real.sqrt (ChainDrift.horizon n) * WindowR.YR n = a0C n - WindowR.mR n :=
    WindowR.sqrtT_mul_YR hn3
  have hu : 0 < a0C n - Real.sqrt (ChainDrift.horizon n) * WindowR.YR n := by
    rw [hgap]; linarith [hmRpos]
  set v : ℝ := WindowR.reachNum n with hv
  have hvdef : v = subst (a0C n) (Real.sqrt (ChainDrift.horizon n)) (WindowR.YR n) := rfl
  have hvpos : 0 < v := by rw [hvdef]; exact subst_pos hu
  have hWv : W = v / α + Real.sqrt n / 2 := by rw [hWdef]; exact WindowR.windowR_eq α n
  set Yt : ℝ := yOf (a0C n) t v with hYt
  have hYtmul : Yt * Real.sqrt t = a0C n - WindowR.mR n := by
    rw [hYt, yOf_mul_sqrt ht, hvdef, subst_sq_inv hu, hgap]; ring
  have hY1 : Yt * Real.sqrt t ≤ 1 / 2 := by
    rw [hYtmul]; linarith [WindowR.mR_ge hn]
  have hYt0 : 0 ≤ Yt := le_of_mul_le_mul_right
    (by rw [zero_mul, hYtmul]; linarith [WindowR.mR_lt_one hn, a0C_ge_one (by omega : 2 ≤ n)])
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
    exact two_logn_sqrtT_le_gap hn
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


/-! ## 8. The bound uniformly in `t ∈ (0, T]`, at the reach window -/

/-- The reach window is nonnegative. -/
theorem windowR_nonneg {α : ℝ} {n : ℕ} (hn : 2073600 ≤ n) (hα : 0 < α) :
    0 ≤ WindowR.windowR α n := by
  rw [WindowR.windowR_eq]
  have h1 : 1 < WindowR.reachNum n := WindowR.one_lt_reachNum hn
  have h0 : (0 : ℝ) ≤ WindowR.reachNum n := by linarith
  have hd : (0 : ℝ) ≤ WindowR.reachNum n / α := div_nonneg h0 hα.le
  have hs : (0 : ℝ) ≤ Real.sqrt n / 2 := by positivity
  linarith

/-- **Lemma 4.3 at the reach window, uniformly in `t`.**  The `t ≥ t₀` branch is `hgbound_at'`;
below `t₀ = 16/n²` the profile's monotonicity in `t` reduces to the value at `t₀`, where
`e^{n²t₀/8} = e²`.  One constant `e²·C₁ᴿ` serves both.  The `n²` in the exponent is untouched. -/
theorem hgbound'_of_chain' {α W : ℝ} {n : ℕ} (hn : 2073600 ≤ n) (hα : 0 < α)
    (hdef : (n : ℝ) * (α * Real.sqrt n / 2) ≤ 1 / 4)
    (hWdef : W = WindowR.windowR α n) :
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
  · refine le_trans (hgbound_at' hn hα hdef hWdef hbig ht.2) (ENNReal.ofReal_le_ofReal ?_)
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
    refine le_trans hmono (le_trans (hgbound_at' hn hα hdef hWdef le_rfl ht0T)
      (ENNReal.ofReal_le_ofReal ?_))
    rw [show (n : ℝ) ^ 2 * (16 / (n : ℝ) ^ 2) / 8 = 2 by field_simp; norm_num]
    calc C1cR (a0C n) α n * Real.exp 2 = Real.exp 2 * C1cR (a0C n) α n * 1 := by ring
      _ ≤ Real.exp 2 * C1cR (a0C n) α n * Real.exp ((n : ℝ) ^ 2 / 8 * t) := by gcongr

/-! ## 9. Lemma 4.3's Bochner output at the reach window -/

/-- Lemma 4.3's radial profile at the reach window. -/
noncomputable def fR (α : ℝ) (n : ℕ) : ℝ → ℝ := fun r =>
  ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
    profile (a0C n) α (WindowR.windowR α n) n t r

/-- Lemma 4.3's per-`t` constant at the reach window, with the small-`t` branch's `e²`. -/
noncomputable def C1R (α : ℝ) (n : ℕ) : ℝ := Real.exp 2 * C1cR (a0C n) α n

theorem fR_nonneg (α : ℝ) (n : ℕ) (r : ℝ) : 0 ≤ fR α n r :=
  setIntegral_nonneg measurableSet_Ioc (fun t _ => profile_nonneg t r)

theorem C1R_pos {α : ℝ} {n : ℕ} (hn : 2 ≤ n) (hα : 0 < α) : 0 < C1R α n :=
  mul_pos (Real.exp_pos 2)
    (C1cR_pos (by omega) hα (lt_of_lt_of_le zero_lt_one (a0C_ge_one hn)))

theorem eight_sub_pos {n : ℕ} (hn : 2 ≤ n) : (0 : ℝ) < 8 - 8 / (n : ℝ) ^ 2 := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1 : (0 : ℝ) < (n : ℝ) ^ 2 := by nlinarith
  have h2 : 8 / (n : ℝ) ^ 2 ≤ 2 := by
    rw [div_le_iff₀ h1]; nlinarith
  linarith

/-- **Lemma 4.3 at the reach window, as `Params.radial_bound`.**  Tonelli over `(0,T]` turns the
uniform fixed-`t` bound into the radial bound, with `C = e²·C₁ᴿ·(8 − 8/n²)` — the `t`-integral
`∫₀ᵀ e^{n²t/8} dt = 8 − 8/n²` is exact, so the `n²` of the horizon cancels the `n⁻²` of the
exponent and the constant is absolute.  Kill rule 2 does not fire. -/
theorem radial_bound_of_chain' {α W : ℝ} {n : ℕ} (hn : 2073600 ≤ n) (hα : 0 < α)
    (hdef : (n : ℝ) * (α * Real.sqrt n / 2) ≤ 1 / 4)
    (hWdef : W = WindowR.windowR α n) :
    ∫ y in Ioi (0 : ℝ), y ^ (n - 1) *
        (∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n), profile (a0C n) α W n t y)
      ≤ Real.exp 2 * C1cR (a0C n) α n * (8 - 8 / (n : ℝ) ^ 2) := by
  have hn0 : 0 < n := by omega
  have hC0 : 0 ≤ Real.exp 2 * C1cR (a0C n) α n :=
    mul_nonneg (Real.exp_pos 2).le (C1cR_nonneg hα)
  have hT0 : (0 : ℝ) ≤ ChainDrift.horizon n := T_nonneg (by omega)
  have hW0 : 0 ≤ W := by rw [hWdef]; exact windowR_nonneg hn hα
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
    (hgbound'_of_chain' hn hα hdef hWdef)

/-- **The radial bound in the `4·profile` shape brief 81's `params_of_raw2R_of_radial` consumes.**
The right-hand side is literally `TailAtStepR2.fR4 α n`, and `C = 4·C1R·(8 − 8/n²)`. -/
theorem radial_bound4_of_chain' {α : ℝ} {n : ℕ} (hn : 2073600 ≤ n) (hα : 0 < α)
    (hdef : (n : ℝ) * (α * Real.sqrt n / 2) ≤ 1 / 4) :
    ∫ y in Ioi (0 : ℝ), y ^ (n - 1) *
        (4 * ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
          profile (a0C n) α (WindowR.windowR α n) n t y)
      ≤ 4 * C1R α n * (8 - 8 / (n : ℝ) ^ 2) := by
  have h := radial_bound_of_chain' (α := α) (W := WindowR.windowR α n) hn hα hdef rfl
  have heq : ∀ y : ℝ, y ^ (n - 1) *
      (4 * ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
        profile (a0C n) α (WindowR.windowR α n) n t y)
      = 4 * (y ^ (n - 1) * ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
        profile (a0C n) α (WindowR.windowR α n) n t y) := by
    intro y; ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun y _ => heq y),
    MeasureTheory.integral_const_mul]
  have h4 := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 4)
  simp only [C1R]
  linarith

theorem C4_pos {α : ℝ} {n : ℕ} (hn : 2073600 ≤ n) (hα : 0 < α) :
    0 < 4 * C1R α n * (8 - 8 / (n : ℝ) ^ 2) :=
  mul_pos (by linarith [C1R_pos (α := α) (n := n) (by omega) hα]) (eight_sub_pos (by omega))

/-! ## 10. The price of the repair: `C1R ≤ 1.01·C1C` -/

theorem hundred_le_Kc : (100 : ℝ) ≤ Kc := by
  have he : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have h6 : Real.exp 6 = Real.exp 2 * (Real.exp 2 * Real.exp 2) := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  have he2 : (7 : ℝ) < Real.exp 2 := by nlinarith [Real.exp_pos 1]
  have he6 : (300 : ℝ) < Real.exp 6 := by nlinarith [Real.exp_pos 2]
  have hrest : 0 ≤ Real.exp 3 * (2 / Real.sqrt (2 * π) + 2) + 2 * Real.exp 3 := by positivity
  unfold Kc; linarith

/-- **The repair costs at most 1%.**  `C₁ᴿ − C₁ = e^{1/2}/(n·αⁿ)` while `C₁ ≥ e^{1/2}K/(n·αⁿ)`
with `K ≥ 100`, so the reach window's constant is within a factor `1 + 1/K ≤ 1.01`. -/
theorem C1cR_le {a₀ α : ℝ} {n : ℕ} (hn : 0 < n) (hα : 0 < α) (_ha₀ : 0 < a₀) :
    C1cR a₀ α n ≤ 1.01 * C1c a₀ α n := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hA : (0 : ℝ) ≤ rhoC a₀ α n ^ n / (2 * (n : ℝ)) :=
    div_nonneg (pow_nonneg (rhoC_nonneg hα) _) (by positivity)
  have hB : (0 : ℝ) < Real.exp (1 / 2) / ((n : ℝ) * α ^ n) := by positivity
  have hK : (100 : ℝ) ≤ Kc := hundred_le_Kc
  unfold C1cR C1c KcR
  nlinarith [hA, hB, hK]

/-- **The repair costs at most 1%**, in the shipped constant. -/
theorem C1R_le {α : ℝ} {n : ℕ} (hn : 2073600 ≤ n) (hα : 0 < α) :
    C1R α n ≤ 1.01 * C1C α n := by
  have h := C1cR_le (a₀ := a0C n) (α := α) (n := n) (by omega) hα
    (lt_of_lt_of_le zero_lt_one (a0C_ge_one (by omega)))
  have he : (0 : ℝ) < Real.exp 2 := Real.exp_pos 2
  unfold C1R C1C
  nlinarith [h, he]

/-! ## 10b. The radial bound at the single time `t = T` (report 74 §4's terminal summand) -/

/-- **Lemma 4.3 at `t = T` alone, at the reach window.**  `e^{n²T/8} = e^{2·log n} = n²` exactly,
so the terminal summand's constant is `C₁ᴿ·n²`.  Report 74 §4's combined weight needs this. -/
theorem radial_bound_terminal {α : ℝ} {n : ℕ} (hn : 2073600 ≤ n) (hα : 0 < α)
    (hdef : (n : ℝ) * (α * Real.sqrt n / 2) ≤ 1 / 4) :
    ∫ y in Ioi (0 : ℝ), y ^ (n - 1) *
        profile (a0C n) α (WindowR.windowR α n) n (ChainDrift.horizon n) y
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
  have hW0 : (0 : ℝ) ≤ WindowR.windowR α n := windowR_nonneg hn hα
  refine radial_bound_of_lintegral (fun r => profile_nonneg _ r) hC0
    (integrableOn_profile_radial hW0 _) ?_
  have hle := hgbound_at' (α := α) (W := WindowR.windowR α n)
    (t := ChainDrift.horizon n) hn hα hdef rfl ht0T le_rfl
  rwa [hexp] at hle

/-! ## 11. The chain's input at the reach window, and `Params` -/

open Submission.L10.ChainDataInst Submission.L10.Tiling
open Submission.L10.Section5 Submission.L10.ConstructionA

/-- **The chain's input at the reach window.**  `Lemma43Uniform.ChainInput` with `windowC`
replaced by `WindowR.windowR` and `fC` by `fR`; nothing else moves. -/
structure ChainInputR (p n : ℕ) where
  alpha : ℝ
  alpha_pos : 0 < alpha
  alpha_norm : alpha ^ n * ((p ^ (n - 1) : ℕ) : ℝ) = kappa n
  R : ℝ
  R_nonneg : 0 ≤ R
  R_scaled : alpha * R ≤ 1 - 1 / (n : ℝ)
  R_lt_p : R < (p : ℝ)
  tiling_defect : (n : ℝ) * (alpha * Real.sqrt n / 2) ≤ 1 / 4
  window_lt_p : WindowR.windowR alpha n < (p : ℝ)
  w : (Fin n → ℤ) → ℝ≥0∞
  supp : Finset (Fin n → ℤ)
  supp_ne_zero : ∀ y ∈ supp, y ≠ 0
  supp_radius : ∀ y ∈ supp, ‖toE n y‖ ≤ WindowR.windowR alpha n
  dom : ∀ y ∈ supp, ∀ x ∈ cube (toE n y), w y ≤ ENNReal.ofReal (fR alpha n ‖x‖)
  arith : (n : ℝ) * kappa n * ((p : ℝ) - 1) * (8 - 8 / (n : ℝ) ^ 2) < 8 * ((p : ℝ) ^ n - 1)

/-- **`Params` at the reach window**, every field supplied — the record filled exactly as
`TailAtStep.params_of_raw2` fills it, with `windowC → WindowR.windowR`, `fC → fR`,
`C1C → C1R`. -/
noncomputable def params_of_chainR {p n : ℕ} [Fact (Nat.Prime p)] (hn : 2073600 ≤ n)
    (I : ChainInputR p n) : Params p n where
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
  windowRadius := WindowR.windowR I.alpha n
  window_lt_p := I.window_lt_p
  f := fR I.alpha n
  f_nonneg := fR_nonneg I.alpha n
  w := I.w
  supp := I.supp
  supp_ne_zero := I.supp_ne_zero
  supp_radius := I.supp_radius
  dom := I.dom
  integrable := integrable_radial_euclidean (a₀ := a0C n) (α := I.alpha)
    (W := WindowR.windowR I.alpha n) (T := ChainDrift.horizon n) (n := n)
    (T_nonneg (by omega : 1 ≤ n))
  C := C1R I.alpha n * (8 - 8 / (n : ℝ) ^ 2)
  radial_bound := radial_bound_of_chain' hn I.alpha_pos I.tiling_defect rfl
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
noncomputable def chainData_of_chainR {p n : ℕ} [Fact (Nat.Prime p)] [NeZero p]
    (hn : 2073600 ≤ n) (I : ChainInputR p n) : ChainData p n :=
  chainData_of_params (params_of_chainR hn I)

/-- §5's line `g`, at the reach window. -/
theorem exists_good_line_of_chainR {p n : ℕ} [Fact (Nat.Prime p)] [NeZero p]
    (hn : 2073600 ≤ n) (I : ChainInputR p n) :
    ∃ g : Fin n → ZMod p, g ≠ 0 ∧
      (∀ y : Fin n → ℤ, y ≠ 0 → ‖toE n y‖ ≤ I.R → y ∉ latZ p n g) ∧
      ∑ y ∈ I.supp.filter (fun y => y ∈ latZ p n g), I.w y
        < ENNReal.ofReal (16 * C1R I.alpha n) :=
  exists_good_line_of_params (params_of_chainR hn I)

end Submission.L10.Lemma43R

-- Vendored from kimihiro64/PrimeNumberTheoremAnd@0f15a38c PrimeNumberTheoremAnd/StrongPNT/ShiftZeroBound.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Submission.PNT.PrimeNumberTheoremAnd.ZetaBounds

/-!
# A uniform logarithmic-derivative bound beside the zeta pole

This module isolates the compactness argument used to control the logarithmic
derivative of the Riemann zeta function on the real interval `(1, 2)`.
-/

@[expose] public section

open Filter Set Complex Real

local notation "ζ" => riemannZeta

local notation "ζ'" => deriv ζ

/-- A uniform bound for the logarithmic derivative of the Riemann zeta function
on the real interval immediately to the right of its pole. -/
lemma ShiftZeroBound :
    ∃ (C : ℝ), C ≥ 1 ∧
      ∀ (δ : ℝ), δ ∈ Ioo 0 1 →
        -(ζ' (1 + δ) / ζ (1 + δ)).re ≤ 1 / δ + C := by
  have zetaAnalyticOnNhd : AnalyticOnNhd ℂ ζ {(1 : ℂ)}ᶜ := DifferentiableOn.analyticOnNhd
    (fun _ hs => (differentiableAt_riemannZeta hs).differentiableWithinAt) isOpen_compl_singleton
  have oneAddContinuous : Continuous (fun x : ℝ => (1 + (x : ℂ))) :=
    Continuous.add continuous_const continuous_ofReal
  have ShiftZeroBoundNear :
      ∃ (C r : ℝ), r ∈ Ioo 0 1 ∧
        ∀ (δ : ℝ), δ ∈ Ioo 0 r →
          -(ζ' (1 + δ) / ζ (1 + δ)).re ≤ 1 / δ + C := by
    obtain ⟨C, hC⟩ := riemannZetaLogDerivResidueBigO.bound
    rcases Metric.mem_nhdsWithin_iff.mp hC with ⟨ε, εpos, hε⟩
    refine ⟨C, min ε (1 / 2), ⟨?_, fun δ δrange => ?_⟩⟩
    · constructor
      · positivity
      · exact lt_of_le_of_lt (min_le_right ε (1 / 2)) (by norm_num)
    · have δin : ((1 : ℂ) + δ) ∈ Metric.ball 1 ε ∩ {1}ᶜ := by
        simp only [mem_inter_iff, Metric.mem_ball, dist_self_add_left, norm_real, norm_eq_abs,
          mem_compl_iff, mem_singleton_iff, add_eq_left, ofReal_eq_zero, abs_lt]
        exact ⟨⟨by linarith [δrange.1], by linarith [δrange.2, min_le_left ε (1 / 2)]⟩,
          by linarith [δrange.1]⟩
      have reBound := (Complex.re_le_norm _).trans (hε δin)
      simp only [Pi.sub_apply, Pi.div_apply, Pi.neg_apply, add_sub_cancel_left, sub_re, inv_re,
        ofReal_re, normSq_ofReal, div_self_mul_self', Pi.one_apply, norm_one, mul_one,
        tsub_le_iff_right] at reBound
      simp only [one_div, ← Complex.neg_re, ← neg_div, add_comm _ C, reBound]
  obtain ⟨C₀, r, rIn, boundNear⟩ := ShiftZeroBoundNear
  have ShiftZeroBoundCompact :
      ∃ (C : ℝ), ∀ (δ : ℝ), δ ∈ Icc r 1 →
        -(ζ' (1 + δ) / ζ (1 + δ)).re ≤ 1 / δ + C := by
    simp only [← sub_le_iff_le_add', ← Complex.neg_re]
    refine ⟨_, fun δ hδ => le_csSup (IsCompact.bddAbove (isCompact_Icc.image_of_continuousOn ?_))
      (Set.mem_image_of_mem _ hδ)⟩
    refine ContinuousOn.add (Complex.continuous_re.comp_continuousOn
      (ContinuousOn.neg (ContinuousOn.div (ContinuousOn.comp zetaAnalyticOnNhd.deriv.continuousOn
        (by apply fun x hx => oneAddContinuous.continuousOn) ?_)
      (ContinuousOn.comp zetaAnalyticOnNhd.continuousOn
        (by apply fun x hx => oneAddContinuous.continuousOn) ?_)
      (fun x hx => riemannZeta_ne_zero_of_one_lt_re ?_)))) (ContinuousOn.neg
        (ContinuousOn.div continuousOn_const continuousOn_id ?_))
    · simp only [MapsTo, mem_Icc, mem_compl_iff, mem_singleton_iff, add_eq_left,
        ofReal_eq_zero, and_imp]
      exact fun x hx _ => by linarith [rIn.1, hx]
    · simp only [MapsTo, mem_Icc, mem_compl_iff, mem_singleton_iff, add_eq_left,
        ofReal_eq_zero, and_imp]
      exact fun x hx _ => by linarith [rIn.1, hx]
    · simp only [add_re, one_re, ofReal_re, lt_add_iff_pos_right]
      linarith [rIn.1, hx.1]
    · simp only [ne_eq]
      exact fun x hx => by linarith [rIn.1, hx.1]
  obtain ⟨C₁, boundCompact⟩ := ShiftZeroBoundCompact
  refine ⟨1 + max |C₀| |C₁|, ?_, fun δ δrange => ?_⟩
  · simp only [ge_iff_le, le_add_iff_nonneg_right, le_sup_iff, abs_nonneg, or_self]
  · by_cases δ_lt_r : δ < r
    · have δIn : δ ∈ Ioo 0 r := by simp only [mem_Ioo, δrange.1, δ_lt_r, and_self]
      apply le_trans (boundNear δ δIn)
      simp only [one_div, add_le_add_iff_left]
      linarith [le_abs_self C₀, le_max_left |C₀| |C₁|]
    · have δIn : δ ∈ Icc r 1 := by
        simp only [mem_Icc, δrange.2.le, ← not_lt, δ_lt_r, not_false_eq_true, and_self]
      apply le_trans (boundCompact δ δIn)
      simp only [one_div, add_le_add_iff_left]
      linarith [le_abs_self C₁, le_max_right |C₀| |C₁|]

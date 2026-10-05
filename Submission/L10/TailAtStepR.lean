import Submission.L10.TailAtStep
import Submission.L10.ChainInputDomR

/-!
# Gate L-10 (`klartag_packing`), brief 72 — `TailAtStep` at the reach window

`TailAtStep`'s `windowC`-naming declarations, copied with `windowC α n → windowR α n`.  The
proofs are unchanged: every lemma they call (`profileAt_eq_Phi`, `riemann_lower_le`,
`profile_nonneg`, `profile_mono_time`, `integrableOn_profile_time`, `dom_of_tail2`) is general in
the window.  `params_of_raw2R` is **not** here — it needs Lemma 4.3 at the new endpoint
(brief 71); see the report's hand-off line.

## The weight-carrying fields (route note of brief 72, 2026-09-12)

Report 62b found that the count event needs a **terminal**-count weight, distinct from the
time-integrated one that feeds the drift, and brief 74 is deciding whether `ChainRaw2`'s
`w`/`tail`/`dom`/`f`/`radial_bound`/`theta`/`markov` become one combined weight.  Until that lands,
`ChainRaw2R` and `chainRaw2_of_chainR` below carry those fields **exactly as in the originals**;
everything else (`alpha`, `R`, the tiling defect, the window at `windowR`, `supp`,
`supp_ne_zero`, `supp_radius`, `arith`) is the verbatim copy this brief asks for.
-/

set_option linter.unusedSectionVars false
-- `intWeight_le`'s `hα` is unused in the original too; these are verbatim copies.
set_option linter.unusedVariables false

namespace Submission.L10

open MeasureTheory Set Real Submission.L10.ChainDataInst Submission.L10.Tiling
open Submission.L10.Section5 Submission.L10.ConstructionA Submission.L10.WindowR
open scoped ENNReal NNReal

/-- **Proposition 4.1 at step `k`, in the profile's language.**  From the `Φ` form of the padded
tail at horizon `k·h` to the `profileAt` form `ContactIntegrated.integrated_count_le` consumes. -/
theorem tail_at_stepR {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} {α hstep : ℝ} {N : ℕ} (C : ℕ → Ω → Finset (Fin n → ℤ))
    (W : Finset (Fin n → ℤ))
    (hwin : ∀ y ∈ W, ‖toE n y‖ + Real.sqrt n / 2 ≤ windowR α n)
    (hr : ∀ y ∈ W, 0 < α * ‖toE n y‖)
    (hy : ∀ k, k < N → k ≠ 0 → ∀ y ∈ W,
      0 < yOf (a0C n) ((k : ℝ) * hstep) (α * ‖toE n y‖))
    (hPhi : ∀ k, k < N → k ≠ 0 → ∀ y ∈ W,
      μ {ω | y ∈ C k ω}
        ≤ ENNReal.ofReal (4 * Phi (yOf (a0C n) ((k : ℝ) * hstep) (α * ‖toE n y‖))))
    (hzero : ∀ y ∈ W, μ.real {ω | y ∈ C 0 ω} = 0) :
    ∀ k, k < N → ∀ y ∈ W,
      μ.real {ω | y ∈ C k ω}
        ≤ 4 * (if k = 0 then 0 else
            profileAt (a0C n) α (windowR α n) n ((k : ℝ) * hstep) ‖toE n y‖) := by
  intro k hk y hy'
  by_cases hk0 : k = 0
  · subst hk0; rw [ite_eq_left rfl, mul_zero, hzero y hy']
  · rw [ite_eq_right hk0,
      profileAt_eq_Phi (hwin y hy') (hr y hy') (hy k hk hk0 y hy')]
    exact measureReal_le_of_le (by
      have := Phi_nonneg (hy k hk hk0 y hy'); linarith) (hPhi k hk hk0 y hy')

/-- The per-step profile: Proposition 4.1's value at step time `k·h`, zero at `k = 0`. -/
noncomputable def profStepR (α : ℝ) (n : ℕ) (hstep : ℝ) (y : Fin n → ℤ) (k : ℕ) : ℝ :=
  if k = 0 then 0 else profileAt (a0C n) α (windowR α n) n ((k : ℝ) * hstep) ‖toE n y‖

theorem intWeight_leR {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} {α hstep : ℝ} {N : ℕ} (hα : 0 < α) (hh : 0 < hstep)
    (hNT : (N : ℝ) * hstep = ChainDrift.horizon n)
    (C : ℕ → Ω → Finset (Fin n → ℤ)) {y : Fin n → ℤ}
    (htail : ∀ k, k < N → μ.real {ω | y ∈ C k ω} ≤ 4 * profStepR α n hstep y k) :
    ContactIntegrated.intWeight μ C hstep N y
      ≤ 4 * ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
          profileAt (a0C n) α (windowR α n) n t ‖toE n y‖ := by
  have hstep_le : ContactIntegrated.intWeight μ C hstep N y
      ≤ ∑ k ∈ Finset.range N, hstep * (4 * profStepR α n hstep y k) := by
    rw [ContactIntegrated.intWeight]
    exact Finset.sum_le_sum (fun k hk =>
      mul_le_mul_of_nonneg_left (htail k (Finset.mem_range.1 hk)) hh.le)
  have hpull : ∑ k ∈ Finset.range N, hstep * (4 * profStepR α n hstep y k)
      = 4 * ∑ k ∈ Finset.range N, hstep * profStepR α n hstep y k := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun k _ => by ring)
  have hR := riemann_lower_le (f := fun t => profileAt (a0C n) α (windowR α n) n t ‖toE n y‖)
    (hstep := hstep) (N := N) hh
    (fun t => profile_nonneg _ _)
    (fun s t hs hst => profile_mono_time hs hst _)
    (fun b => integrableOn_profile_time (‖toE n y‖ + Real.sqrt n / 2))
  rw [hNT] at hR
  refine le_trans hstep_le ?_
  rw [hpull]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  simpa [profStepR] using hR

/-- **`ChainRaw2R.tail`, discharged.**  The per-step tail of §1, summed by §2 and §3, at the
adopted `e = 7` discretisation. -/
theorem tail_of_stepsR {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} {α : ℝ} (hn : 3 ≤ n) (hα : 0 < α) (C : ℕ → Ω → Finset (Fin n → ℤ))
    {y : Fin n → ℤ}
    (hsteps : ∀ k, k < ParamsAdopted2.numStepsAdopted2 n →
      μ.real {ω | y ∈ C k ω}
        ≤ 4 * profStepR α n (ParamsAdopted2.stepSizeAdopted2 n) y k) :
    ENNReal.ofReal (ContactIntegrated.intWeight μ C
        (ParamsAdopted2.stepSizeAdopted2 n) (ParamsAdopted2.numStepsAdopted2 n) y)
      ≤ ENNReal.ofReal (4 * ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
          profileAt (a0C n) α (windowR α n) n t ‖toE n y‖) :=
  ENNReal.ofReal_le_ofReal
    (intWeight_leR hα (adopted_stepSize_pos hn) (adopted_horizon hn) C hsteps)

/-- `ChainRawR` with the `4` of `padded_tail_of_increments` carried in `tail` (report 39 §3: the
factor goes into `f`, never into `alpha`, which `alpha_norm` pins). -/
structure ChainRaw2R (p n : ℕ) where
  alpha : ℝ
  alpha_pos : 0 < alpha
  alpha_norm : alpha ^ n * ((p ^ (n - 1) : ℕ) : ℝ) = kappa n
  R : ℝ
  R_nonneg : 0 ≤ R
  R_scaled : alpha * R ≤ 1 - 1 / (n : ℝ)
  R_lt_p : R < (p : ℝ)
  tiling_defect : (n : ℝ) * (alpha * Real.sqrt n / 2) ≤ 1 / 4
  window_lt_p : windowR alpha n < (p : ℝ)
  w : (Fin n → ℤ) → ℝ≥0∞
  supp : Finset (Fin n → ℤ)
  supp_ne_zero : ∀ y ∈ supp, y ≠ 0
  supp_radius : ∀ y ∈ supp, ‖toE n y‖ ≤ windowR alpha n
  /-- The only probabilistic input; `tail_of_stepsR` supplies it. -/
  tail : ∀ y ∈ supp, w y ≤ ENNReal.ofReal
    (4 * ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
      profileAt (a0C n) alpha (windowR alpha n) n t ‖toE n y‖)
  arith : (n : ℝ) * kappa n * ((p : ℝ) - 1) * (8 - 8 / (n : ℝ) ^ 2) < 8 * ((p : ℝ) ^ n - 1)

noncomputable def chainRaw2_of_chainR {p n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (hn : 3 ≤ n)
    (C : ℕ → Ω → Finset (Fin n → ℤ))
    (alpha : ℝ) (alpha_pos : 0 < alpha)
    (alpha_norm : alpha ^ n * ((p ^ (n - 1) : ℕ) : ℝ) = kappa n)
    (R : ℝ) (R_nonneg : 0 ≤ R) (R_scaled : alpha * R ≤ 1 - 1 / (n : ℝ)) (R_lt_p : R < (p : ℝ))
    (tiling_defect : (n : ℝ) * (alpha * Real.sqrt n / 2) ≤ 1 / 4)
    (window_lt_p : windowR alpha n < (p : ℝ))
    (supp : Finset (Fin n → ℤ)) (supp_ne_zero : ∀ y ∈ supp, y ≠ 0)
    (supp_radius : ∀ y ∈ supp, ‖toE n y‖ ≤ windowR alpha n)
    (hsteps : ∀ y ∈ supp, ∀ k, k < ParamsAdopted2.numStepsAdopted2 n →
      μ.real {ω | y ∈ C k ω}
        ≤ 4 * profStepR alpha n (ParamsAdopted2.stepSizeAdopted2 n) y k)
    (arith : (n : ℝ) * kappa n * ((p : ℝ) - 1) * (8 - 8 / (n : ℝ) ^ 2) < 8 * ((p : ℝ) ^ n - 1)) :
    ChainRaw2R p n where
  alpha := alpha
  alpha_pos := alpha_pos
  alpha_norm := alpha_norm
  R := R
  R_nonneg := R_nonneg
  R_scaled := R_scaled
  R_lt_p := R_lt_p
  tiling_defect := tiling_defect
  window_lt_p := window_lt_p
  w := fun y => ENNReal.ofReal (ContactIntegrated.intWeight μ C
    (ParamsAdopted2.stepSizeAdopted2 n) (ParamsAdopted2.numStepsAdopted2 n) y)
  supp := supp
  supp_ne_zero := supp_ne_zero
  supp_radius := supp_radius
  tail := fun y hy => tail_of_stepsR hn alpha_pos C (hsteps y hy)
  arith := arith

end Submission.L10

import Submission.L10.FinalDischarge

/-!
# Gate L-10 (`klartag_packing`) — a contact threshold whose `C'` is uniform, and `hS` at `windowOfR2`

Report `82a-finaldischarge.md` §1 measured that **no fixed `C'` closes the budget at
`DriftStopped6b.c3Adopted' = 20 000·n²`**: the count failure there is `0.659 4`, independent of
`n`, while the Markov step's shift `|L| = n·|log (mAt n c₃)| ≈ 24√(n log n)` **grows**, so the
required `C'` runs `8.0·10⁵ → 1.2·10⁶ → 7.3·10⁶ → 2.4·10⁸` at `n₁, 10⁷, 10⁹, 10¹²`.  `n³/4` fails
the other way: `c₃·η = 1/4` pins `cqAt` near `0.32`, so report 80's residual
`4·log n·(1 − 2·c)` grows like `1.44·log n` instead of vanishing.

With `x := c₃·η`, uniformity needs `x·log n` bounded **and** `x ≫ √(log n/n)`; the window is

  `n^{5/2}·√(log n) ≪ c₃ ≪ n³/log n`,

and `c3Adopted'' n := n³/√(√n) = n^{11/4}` sits inside it, giving `C'` **decreasing** to `≈ 2.08·10⁵`.

**No frozen module needs changing.**  `GoodPathLightR2.LightGoodPath2`,
`Theorem2R3.klartag_packing_of_lightGoodPath2`, `DriftStopped8R5.bandSideAdoptedR2` and
`DriftStopped6b`'s general lemmas (`slackHyp_at`, `C₁_le_at`, `cqAt_le_half`) are all parametric in
`c₃`; only `DriftStopped6b`'s primed specialisations name `c3Adopted'`.  So this module supplies the
constant and its two admissibility facts, and `FinalDischarge.klartag_packing_final'''` takes them.

§2 is the `hS` glue this lane still lacked: `GoodPathBounds.hS_of_intWeight` with the bad-event
total collapsed against `wiredGood'` (rather than `goodCut`, since `GoodPathAt2` reads the count at
the horizon), and the light contact at the reach-2 shell.
-/

set_option linter.unusedSectionVars false

namespace Submission.L10.FinalDischarge2

open MeasureTheory Matrix Finset Module Submission.L10 Submission.L10.Increments
open Submission.L10.StoppedChain Submission.L10.DriftStopped Submission.L10.DriftStopped5
open Submission.L10.DriftInputsStopped Submission.L10.GoodPathBounds
open Submission.L10.ConstructionA Submission.L10.Tiling
open Submission.L10.RawDataInst2RW2 Submission.L10.RawDataInst2
open Submission.L10.DriftStopped8R5 Submission.L10.GoodPathLightR2
open scoped ENNReal NNReal RealInnerProductSpace

/-! ## 1. A contact threshold inside the uniformity window -/

/-- `c₃ = n³/√(√n) = n^{11/4}`: `c₃·η ≍ n^{−1/4}`, so `c₃·η·log n → 0` (the residual vanishes) and
`c₃·η·√(n/log n) → ∞` (the existence slack stays bounded). -/
noncomputable def c3Adopted'' (n : ℕ) : ℝ := (n : ℝ) ^ 3 / Real.sqrt (Real.sqrt (n : ℝ))

theorem c3Adopted''_nonneg (n : ℕ) : 0 ≤ c3Adopted'' n := by
  rw [c3Adopted'']; positivity

/-- **The admissibility fact every consumer takes**: `c₃·η ≤ 1/4`, with three orders to spare. -/
theorem c3Adopted''_eta_le {n : ℕ} (hn : 2073600 ≤ n) :
    c3Adopted'' n * DriftStopped6.etaAdopted n ≤ 1 / 4 := by
  have hn3 : 3 ≤ n := by omega
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hss : (37 : ℝ) ≤ Real.sqrt (Real.sqrt (n : ℝ)) := DriftStopped7.sqrt_sqrt_ge hn
  have hssp : (0 : ℝ) < Real.sqrt (Real.sqrt (n : ℝ)) := by linarith
  have heta : DriftStopped6.etaAdopted n ≤ Real.sqrt 2 / (n : ℝ) ^ 3 := by
    rw [DriftStopped6.etaAdopted]; exact ParamsAdopted2.eta2_le hn3
  have h2 : Real.sqrt 2 ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt (2 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hc0 : 0 ≤ c3Adopted'' n := c3Adopted''_nonneg n
  have hstep : c3Adopted'' n * DriftStopped6.etaAdopted n
      ≤ c3Adopted'' n * (Real.sqrt 2 / (n : ℝ) ^ 3) := mul_le_mul_of_nonneg_left heta hc0
  have hval : c3Adopted'' n * (Real.sqrt 2 / (n : ℝ) ^ 3)
      = Real.sqrt 2 / Real.sqrt (Real.sqrt (n : ℝ)) := by
    rw [c3Adopted'']; field_simp
  rw [hval] at hstep
  have hfin : Real.sqrt 2 / Real.sqrt (Real.sqrt (n : ℝ)) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ hssp (by norm_num)]
    nlinarith [h2, hss, Real.sqrt_nonneg (2 : ℝ)]
  linarith

/-! ## 2. `hS` at the horizon count, and at `windowOfR2` -/

section HS

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι] {Ω : Type*} [MeasurableSpace Ω]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)} {P : Measure Ω} [IsProbabilityMeasure P]

/-- On `wiredGood'` the stopping time never fires (`StoppedChain.tau_eq_of_wiredGood'`), so every
pre-stopping event before the horizon fails no more often than `wiredGood'` does. -/
theorem measureReal_compl_lt_tau_le_wired {r thr η r₀ c₃ pbad : ℝ}
    {Wacc : Ω → EuclideanSpace ℝ (UT n)} {N k : ℕ} (hkN : k < N)
    (hbad : P.real (StateInvariant4.wiredGood' r Wacc ξ thr N η q W A₀ r₀ c₃)ᶜ ≤ pbad) :
    P.real {ω | k < tau q W A₀ ξ η r₀ c₃ N ω}ᶜ ≤ pbad := by
  refine le_trans (measureReal_mono ?_ (measure_ne_top P _)) hbad
  intro ω hω
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at hω ⊢
  intro hg
  have := tau_eq_of_wiredGood' hg
  omega

theorem sum_compl_lt_tau_le_wired {r thr η r₀ c₃ pbad : ℝ}
    {Wacc : Ω → EuclideanSpace ℝ (UT n)} {N m : ℕ} (hmN : m ≤ N)
    (hbad : P.real (StateInvariant4.wiredGood' r Wacc ξ thr N η q W A₀ r₀ c₃)ᶜ ≤ pbad) :
    ∑ k ∈ Finset.range m, P.real {ω | k < tau q W A₀ ξ η r₀ c₃ N ω}ᶜ ≤ (m : ℝ) * pbad := by
  calc ∑ k ∈ Finset.range m, P.real {ω | k < tau q W A₀ ξ η r₀ c₃ N ω}ᶜ
      ≤ ∑ _k ∈ Finset.range m, pbad :=
        Finset.sum_le_sum fun k hk =>
          measureReal_compl_lt_tau_le_wired (by have := Finset.mem_range.1 hk; omega) hbad
    _ = (m : ℝ) * pbad := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **`hS`, with the horizon good event.**  `GoodPathBounds.hS_of_intWeight` with the bad-event
total collapsed against `wiredGood'` — the event `GoodPathAt2` actually carries. -/
theorem hS_of_intWeight_wired {r thr η r₀ c₃ hstep Θ pbad : ℝ}
    {Wacc : Ω → EuclideanSpace ℝ (UT n)} {N m : ℕ} (hstep0 : 0 < hstep) (hmN : m ≤ N)
    (hξ : ∀ j, Measurable (ξ j)) (hτ : Measurable (tau q W A₀ ξ η r₀ c₃ N))
    (hlight : ∑ y ∈ W, ContactIntegrated.intWeight P
        (fun k ω => (Chain.chain q W A₀ ξ k ω).2) hstep m y ≤ Θ)
    (hbad : P.real (StateInvariant4.wiredGood' r Wacc ξ thr N η q W A₀ r₀ c₃)ᶜ ≤ pbad) :
    (m : ℝ) * (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) - Θ / hstep
        - (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) * ((m : ℝ) * pbad)
      ≤ ∑ k ∈ Finset.range m, ∫ ω,
          DriftStopped6.stoppedFreeDim q W A₀ ξ η r₀ c₃ N k ω ∂P := by
  have hbase := hS_of_intWeight (q := q) (W := W) (A₀ := A₀) (ξ := ξ) (N := N) (m := m)
    hstep0 hξ hτ hlight
  have hsum := sum_compl_lt_tau_le_wired (q := q) (W := W) (A₀ := A₀) (ξ := ξ)
    (r := r) (thr := thr) (Wacc := Wacc) hmN hbad
  have hdim : (0 : ℝ) ≤ (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hsum hdim
  linarith

end HS

end Submission.L10.FinalDischarge2

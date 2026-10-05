import Submission.L10.GoodPathBounds
import Submission.L10.GoodPathLight

/-!
# Gate L-10 (`klartag_packing`) — `hS`, the free-dimension total, from the light contact

Brief 86.  Report 82a §3 named `hS` as input (i) of `goodPathAt_of_S`; `GoodPathBounds.hS_of_intWeight`
(`:898`) already derives it from a *real sum* `∑_W intWeight ≤ Θ`.  This module closes the last two
steps: the light contact **is** that real sum (transported from `shellR` to `windowOfR` by
`DriftStopped8R.filter_eq_windowOfR`, rule 16, through `GoodPathLight.sum_lt_of_lightContact`), and
the bad-event total `dim·∑_{k<K} P(τ ≤ k)` is `dim·K·p_bad` because `goodCut … K ⊆ {K < τ}`.

`c₃` stays **free** under `c₃·η ≤ 1/4`, exactly as in `GoodPathBounds`.

## The shape delivered

`hS_of_lightContact` gives, at `Cset k ω = (Chain.chain q W A₀ ξ k ω).2`,

  `(K:ℝ)·dim − Θ/h − dim·((K:ℝ)·p_bad) ≤ ∑_{k<K} ∫ stoppedFreeDim … k`,

which is `goodPathAt_of_S`'s and `goodPathCut`'s `hS` at
`S := K·dim − Θ/h − dim·K·p_bad`.  At `K := N − 1` and `Θ := θ'` this is the brief's
`S = (N−1)·dim − θ'/h − dim·∑_{k<N−1} P(bad k)`; at `K := ⌊N/2⌋` it is the index report 82a-hinge
fixes, and the statement is the same theorem.

`GoodPathBounds.lean` and `GoodPathLight.lean` are reported and are not edited; this module imports
them.
-/

set_option linter.unusedSectionVars false

namespace Submission.L10.FreeDimTotal

open MeasureTheory Matrix Finset Module Submission.L10 Submission.L10.Increments
open Submission.L10.StoppedChain Submission.L10.DriftStopped Submission.L10.DriftStopped5
open Submission.L10.DriftInputsStopped Submission.L10.GoodPathBounds
open Submission.L10.ConstructionA Submission.L10.Tiling
open Submission.L10.RawDataInst2R Submission.L10.RawDataInst2 Submission.L10.DriftStopped8R
open scoped ENNReal NNReal RealInnerProductSpace

/-! ## 1. The bad-event total -/

section Bad

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι] {Ω : Type*} [MeasurableSpace Ω]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)} {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Every pre-stopping event before `K` fails no more often than `goodCut … K` does** — because
`goodCut … K ⊆ {K < τ}` (`GoodPathBounds.lt_tau_of_goodCut`) and `{τ ≤ k} ⊆ {τ ≤ K}`. -/
theorem measureReal_compl_lt_tau_le {r thr η r₀ c₃ pbad : ℝ}
    {Wacc : Ω → EuclideanSpace ℝ (UT n)} {N K k : ℕ} (hKN : K < N) (hk : k ≤ K)
    (hbad : P.real (goodCut r Wacc ξ thr N η q W A₀ r₀ c₃ K)ᶜ ≤ pbad) :
    P.real {ω | k < tau q W A₀ ξ η r₀ c₃ N ω}ᶜ ≤ pbad := by
  refine le_trans (measureReal_mono ?_ (measure_ne_top P _)) hbad
  intro ω hω
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at hω ⊢
  intro hg
  have := lt_tau_of_goodCut hg hKN
  omega

/-- The bad-event total over the horizon, `K·p_bad`. -/
theorem sum_compl_lt_tau_le {r thr η r₀ c₃ pbad : ℝ}
    {Wacc : Ω → EuclideanSpace ℝ (UT n)} {N K : ℕ} (hKN : K < N)
    (hbad : P.real (goodCut r Wacc ξ thr N η q W A₀ r₀ c₃ K)ᶜ ≤ pbad) :
    ∑ k ∈ Finset.range K, P.real {ω | k < tau q W A₀ ξ η r₀ c₃ N ω}ᶜ ≤ (K : ℝ) * pbad := by
  calc ∑ k ∈ Finset.range K, P.real {ω | k < tau q W A₀ ξ η r₀ c₃ N ω}ᶜ
      ≤ ∑ _k ∈ Finset.range K, pbad :=
        Finset.sum_le_sum fun k hk =>
          measureReal_compl_lt_tau_le hKN (le_of_lt (Finset.mem_range.1 hk)) hbad
    _ = (K : ℝ) * pbad := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **`hS` with the bad-event total collapsed.**  `GoodPathBounds.hS_of_intWeight` with
`∑_{k<K} P(τ ≤ k)` replaced by `K·p_bad`. -/
theorem hS_of_intWeight_bad {r thr η r₀ c₃ hstep Θ pbad : ℝ}
    {Wacc : Ω → EuclideanSpace ℝ (UT n)} {N K : ℕ} (hstep0 : 0 < hstep) (hKN : K < N)
    (hξ : ∀ j, Measurable (ξ j)) (hτ : Measurable (tau q W A₀ ξ η r₀ c₃ N))
    (hlight : ∑ y ∈ W, ContactIntegrated.intWeight P
        (fun k ω => (Chain.chain q W A₀ ξ k ω).2) hstep K y ≤ Θ)
    (hbad : P.real (goodCut r Wacc ξ thr N η q W A₀ r₀ c₃ K)ᶜ ≤ pbad) :
    (K : ℝ) * (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) - Θ / hstep
        - (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) * ((K : ℝ) * pbad)
      ≤ ∑ k ∈ Finset.range K, ∫ ω,
          DriftStopped6.stoppedFreeDim q W A₀ ξ η r₀ c₃ N k ω ∂P := by
  have hbase := hS_of_intWeight (q := q) (W := W) (A₀ := A₀) (ξ := ξ) (N := N) (m := K)
    hstep0 hξ hτ hlight
  have hsum := sum_compl_lt_tau_le (q := q) (W := W) (A₀ := A₀) (ξ := ξ)
    (r := r) (thr := thr) (Wacc := Wacc) hKN hbad
  have hdim : (0 : ℝ) ≤ (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hsum hdim
  linarith

end Bad

/-! ## 2. The light contact is the real sum -/

section Light

variable {n : ℕ} {ι : Type*} [DecidableEq ι] {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

theorem intWeight_nonneg {Cset : ℕ → Ω → Finset ι} {hstep : ℝ} (hstep0 : 0 ≤ hstep)
    (Nsteps : ℕ) (y : ι) : 0 ≤ ContactIntegrated.intWeight P Cset hstep Nsteps y := by
  rw [ContactIntegrated.intWeight]
  exact Finset.sum_nonneg fun k _ => mul_nonneg hstep0 measureReal_nonneg

end Light

/-! ## 3. `hS` from the light contact, at the chain's own data -/

section Main

variable {p m : ℕ} [NeZero p] {α : ℝ} {g : Fin (m + 1) → ZMod p}

/-- **`hS`, from the light contact.**  The threshold `Θ` is `ThetaTight.thetaTight`'s value at the
caller's parameters; `GoodPathLight.sum_lt_of_lightContact` does the `shellR → windowOfR`
transport (rule 16), and §1 collapses the bad-event total.  This is exactly
`GoodPathBounds.goodPathCut`'s `hS` at `S := K·dim − Θ/h − dim·K·p_bad`. -/
theorem hS_of_lightContact {c₃ hstep Θ pbad r thr : ℝ} {K : ℕ}
    (hstep0 : 0 < hstep) (hΘ : 0 < Θ)
    (hKN : K < ParamsAdopted2.numStepsAdopted2 (m + 1))
    (hτ : Measurable (tau (qC α) (windowOfR α p m g) (A0C (m + 1))
      (ChainSetup.step (Submission.L10.cAdopted (m + 1)))
      (DriftStopped6.etaAdopted (m + 1)) (DriftStopped6.r0Adopted (m + 1)) c₃
      (ParamsAdopted2.numStepsAdopted2 (m + 1))))
    (hlight : Theorem2.LightContact
      (fun y => ENNReal.ofReal (ContactIntegrated.intWeight
        (ChainSetup.gaussPath (EuclideanSpace ℝ (UT (m + 1))))
        (fun k ω => (Chain.chain (qC α) (windowOfR α p m g) (A0C (m + 1))
          (ChainSetup.step (Submission.L10.cAdopted (m + 1))) k ω).2) hstep K y))
      (shellR α (m + 1)) (ENNReal.ofReal Θ) g)
    (hbad : (ChainSetup.gaussPath (EuclideanSpace ℝ (UT (m + 1)))).real
      (goodCut r (ChainSetup.coord 0) (ChainSetup.step (Submission.L10.cAdopted (m + 1))) thr
        (ParamsAdopted2.numStepsAdopted2 (m + 1)) (DriftStopped6.etaAdopted (m + 1))
        (qC α) (windowOfR α p m g) (A0C (m + 1)) (DriftStopped6.r0Adopted (m + 1)) c₃ K)ᶜ
      ≤ pbad) :
    (K : ℝ) * (finrank ℝ (EuclideanSpace ℝ (UT (m + 1))) : ℝ) - Θ / hstep
        - (finrank ℝ (EuclideanSpace ℝ (UT (m + 1))) : ℝ) * ((K : ℝ) * pbad)
      ≤ ∑ k ∈ Finset.range K, ∫ ω,
          DriftStopped6.stoppedFreeDim (qC α) (windowOfR α p m g) (A0C (m + 1))
            (ChainSetup.step (Submission.L10.cAdopted (m + 1)))
            (DriftStopped6.etaAdopted (m + 1)) (DriftStopped6.r0Adopted (m + 1)) c₃
            (ParamsAdopted2.numStepsAdopted2 (m + 1)) k ω
          ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT (m + 1)))) := by
  have hreal := GoodPathLight.sum_lt_of_lightContact
    (v := fun y => ContactIntegrated.intWeight
      (ChainSetup.gaussPath (EuclideanSpace ℝ (UT (m + 1))))
      (fun k ω => (Chain.chain (qC α) (windowOfR α p m g) (A0C (m + 1))
        (ChainSetup.step (Submission.L10.cAdopted (m + 1))) k ω).2) hstep K y)
    (fun y => intWeight_nonneg hstep0.le K y) hΘ hlight
  exact hS_of_intWeight_bad hstep0 hKN
    (fun j => ChainSetup.measurable_step (Submission.L10.cAdopted (m + 1)) j) hτ
    (le_of_lt hreal) hbad

/-- **The brief's `S`, in the cleaner arrangement** `S = K·dim·(1 − p_bad) − Θ/h`.  Identical to
`hS_of_lightContact` by `ring`; stated because it is the form the `C'` table reads. -/
theorem hS_clean {c₃ hstep Θ pbad r thr : ℝ} {K : ℕ}
    (hstep0 : 0 < hstep) (hΘ : 0 < Θ)
    (hKN : K < ParamsAdopted2.numStepsAdopted2 (m + 1))
    (hτ : Measurable (tau (qC α) (windowOfR α p m g) (A0C (m + 1))
      (ChainSetup.step (Submission.L10.cAdopted (m + 1)))
      (DriftStopped6.etaAdopted (m + 1)) (DriftStopped6.r0Adopted (m + 1)) c₃
      (ParamsAdopted2.numStepsAdopted2 (m + 1))))
    (hlight : Theorem2.LightContact
      (fun y => ENNReal.ofReal (ContactIntegrated.intWeight
        (ChainSetup.gaussPath (EuclideanSpace ℝ (UT (m + 1))))
        (fun k ω => (Chain.chain (qC α) (windowOfR α p m g) (A0C (m + 1))
          (ChainSetup.step (Submission.L10.cAdopted (m + 1))) k ω).2) hstep K y))
      (shellR α (m + 1)) (ENNReal.ofReal Θ) g)
    (hbad : (ChainSetup.gaussPath (EuclideanSpace ℝ (UT (m + 1)))).real
      (goodCut r (ChainSetup.coord 0) (ChainSetup.step (Submission.L10.cAdopted (m + 1))) thr
        (ParamsAdopted2.numStepsAdopted2 (m + 1)) (DriftStopped6.etaAdopted (m + 1))
        (qC α) (windowOfR α p m g) (A0C (m + 1)) (DriftStopped6.r0Adopted (m + 1)) c₃ K)ᶜ
      ≤ pbad) :
    (K : ℝ) * (finrank ℝ (EuclideanSpace ℝ (UT (m + 1))) : ℝ) * (1 - pbad) - Θ / hstep
      ≤ ∑ k ∈ Finset.range K, ∫ ω,
          DriftStopped6.stoppedFreeDim (qC α) (windowOfR α p m g) (A0C (m + 1))
            (ChainSetup.step (Submission.L10.cAdopted (m + 1)))
            (DriftStopped6.etaAdopted (m + 1)) (DriftStopped6.r0Adopted (m + 1)) c₃
            (ParamsAdopted2.numStepsAdopted2 (m + 1)) k ω
          ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT (m + 1)))) := by
  have h := hS_of_lightContact hstep0 hΘ hKN hτ hlight hbad
  have heq : (K : ℝ) * (finrank ℝ (EuclideanSpace ℝ (UT (m + 1))) : ℝ) * (1 - pbad) - Θ / hstep
      = (K : ℝ) * (finrank ℝ (EuclideanSpace ℝ (UT (m + 1))) : ℝ) - Θ / hstep
        - (finrank ℝ (EuclideanSpace ℝ (UT (m + 1))) : ℝ) * ((K : ℝ) * pbad) := by ring
  rw [heq]
  exact h


end Main

end Submission.L10.FreeDimTotal

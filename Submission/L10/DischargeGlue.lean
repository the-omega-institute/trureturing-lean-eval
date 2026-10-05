import Submission.L10.Discharge
import Submission.L10.StepGlue

/-!
# Gate L-10 (`klartag_packing`) — brief 25's route correction: onto `StepGlue.chainGood`

`Submission/L10/Discharge.lean` (report 25) built its own good event,
`Discharge.chainGood = GoodEvent.goodEvent ∩ StepInputs2.stepGood`, whose accumulated half lives on
the **matrix** carrier.  Brief 15's `Submission/L10/StepGlue.lean` had meanwhile put the whole
event on the **`UT n`** carrier, `StepGlue.chainGood = StepInputs.goodEventUT ∩ stepGood`, which is
the currency the rest of the chain uses (`Increments`, `StepInputs2`, `ChainWiring`).  The
coordinator's route addition is to build on the glue's event.

`Discharge.lean` is reported and frozen (rule 5), so the correction lives here.

**`Discharge.chainGood` and `Discharge.measureReal_compl_chainGood_chainScale` are superseded** by
`StepGlue.chainGood` and `measureReal_compl_chainGood_chainScale` below; nothing else in
`Discharge.lean` is affected, because everything else there depends on the good event only through
its *second* component, `StepInputs2.stepGood`, which the two events share.  In particular
`Discharge.hpt_step`, `Discharge.eta_le`, `Discharge.stepGood_cost_le` and `Discharge.failure_le`
carry over unchanged and are reused below.

## Contents

1. The failure probability of `StepGlue.chainGood` at the chain's scale, and at the adopted
   parameters — the same `(33 n⁷ log n + 4)·e^{−n}` as report 25 §3, now on the glue's event.
2. `StateInvariant` and `hpt` restated on `StepGlue.chainGood`.
3. H3 in the chain's own notation, from `StepGlue.condExp_norm_sq_starProjection_smul_random`.
-/

set_option linter.unusedSectionVars false

namespace Submission.L10.DischargeGlue

open MeasureTheory ProbabilityTheory Matrix Metric Finset Module
open scoped ENNReal NNReal RealInnerProductSpace
open Submission.L10 Submission.L10.Increments

variable {n : ℕ}

/-! ## 1. The glue's good event at the chain's scale -/

section Failure

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The failure probability of `StepGlue.chainGood` at the chain's scale.**  The accumulated half
is `StepInputs.measureReal_compl_goodEventUT_le` at `s = 1`; the per-step half is
`StepInputs2.measureReal_compl_stepGood_chainScale` at `η = √(2 v d n)`.  Both come out `e^{−n}`. -/
theorem measureReal_compl_chainGood_chainScale {r : ℝ} (hr : 0 < r)
    {Wacc : Ω → EuclideanSpace ℝ (UT n)} (hW : Measurable Wacc)
    (hWlaw : P.map Wacc = stdGaussian (EuclideanSpace ℝ (UT n)))
    {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)} {v : ℝ≥0} (hv : 0 < v) (hn : 0 < n)
    (hlaw : ∀ k, ∀ p : UT n, P.map (fun ω => ξ k ω p) = gaussianReal 0 v) (N : ℕ) :
    P.real (StepGlue.chainGood r Wacc ξ (6 * r * 1 * Real.sqrt n) N
        (Real.sqrt (2 * (v : ℝ) * (Fintype.card (UT n) : ℝ) * (n : ℝ))))ᶜ
      ≤ 4 * Real.exp (-(n : ℝ))
        + (N : ℝ) * ((Fintype.card (UT n) : ℝ) * (2 * Real.exp (-(n : ℝ)))) := by
  have hcompl : (StepGlue.chainGood r Wacc ξ (6 * r * 1 * Real.sqrt n) N
        (Real.sqrt (2 * (v : ℝ) * (Fintype.card (UT n) : ℝ) * (n : ℝ))))ᶜ
      = (StepInputs.goodEventUT r Wacc (6 * r * 1 * Real.sqrt n))ᶜ
        ∪ (StepInputs2.stepGood ξ N
            (Real.sqrt (2 * (v : ℝ) * (Fintype.card (UT n) : ℝ) * (n : ℝ))))ᶜ := by
    rw [StepGlue.chainGood, Set.compl_inter]
  rw [hcompl]
  refine (measureReal_union_le _ _).trans (add_le_add ?_ ?_)
  · have h := StepInputs.measureReal_compl_goodEventUT_le hr hW hWlaw 1 le_rfl
    simpa using h
  · exact StepInputs2.measureReal_compl_stepGood_chainScale hv hn hlaw N

/-- **The same bound at the adopted parameters**, `N = ⌈16 n⁵ log n⌉` and `h = T/N ≤ n⁻⁷`:
`(33 n⁷ log n + 4)·e^{−n}`, which is below `1` from `n = 28` (report 25 §3.2). -/
theorem failure_le_adopted {n : ℕ} (hn : 3 ≤ n) {r : ℝ} (hr : 0 < r)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Wacc : Ω → EuclideanSpace ℝ (UT n)} (hW : Measurable Wacc)
    (hWlaw : P.map Wacc = stdGaussian (EuclideanSpace ℝ (UT n)))
    {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)} {v : ℝ≥0} (hv : 0 < v)
    (hlaw : ∀ k, ∀ p : UT n, P.map (fun ω => ξ k ω p) = gaussianReal 0 v) :
    P.real (StepGlue.chainGood r Wacc ξ (6 * r * 1 * Real.sqrt n)
        (ChainWiring.numStepsAdopted n)
        (Real.sqrt (2 * (v : ℝ) * (Fintype.card (UT n) : ℝ) * (n : ℝ))))ᶜ
      ≤ (33 * (n : ℝ) ^ 7 * Real.log n + 4) * Real.exp (-(n : ℝ)) :=
  Discharge.failure_le hn
    (measureReal_compl_chainGood_chainScale hr hW hWlaw hv (by omega) hlaw _)

end Failure

/-! ## 2. `StateInvariant` and `hpt`, on the glue's event

The only property of the good event either statement uses is its **second** component, and
`Discharge.chainGood` and `StepGlue.chainGood` share it, so the proofs are the same two lines. -/

section Hpt

variable {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [DecidableEq ι]
  {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι}
  {A₀ : EuclideanSpace ℝ (UT n)} {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

/-- **The residual, on `StepGlue.chainGood`.**  Report 25 §5's `Discharge.StateInvariant` with the
good event replaced by the glue's; the mathematical content and the estimate are unchanged (the
Maurey induction over `k`, then the eigenvalue bounds). -/
def StateInvariant (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι)
    (A₀ : EuclideanSpace ℝ (UT n)) (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (r : ℝ)
    (Wacc : Ω → EuclideanSpace ℝ (UT n)) (thr : ℝ) (N : ℕ) (η m M : ℝ) : Prop :=
  ∀ k, k < N → ∀ ω ∈ StepGlue.chainGood r Wacc ξ thr N η,
    Discharge.StateBounds (symMat (Chain.chain q W A₀ ξ k ω).1) m M

/-- **`hpt` on the glue's good event** — the last hypothesis of
`StepInputs2.driftInputs_step_chain`. -/
theorem hpt_of_stateInvariant {r : ℝ} {Wacc : Ω → EuclideanSpace ℝ (UT n)} {thr : ℝ} {N : ℕ}
    {η m M δ : ℝ} (hinv : StateInvariant q W A₀ ξ r Wacc thr N η m M)
    (hδ : η / m ≤ δ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    ∀ k, k < N → ∀ ω ∈ StepGlue.chainGood r Wacc ξ thr N η,
      ChainWiring.logDet (Chain.chain q W A₀ ξ (k + 1) ω).1
        ≤ ChainWiring.logDet (Chain.chain q W A₀ ξ k ω).1
          + ⟪(Chain.freeSub q (Chain.chain q W A₀ ξ k ω).2).starProjection
              (Discharge.matToUT (symMat (Chain.chain q W A₀ ξ k ω).1)⁻¹), ξ k ω⟫
          - (1 / (2 * M ^ 2 * (1 + δ) ^ 2))
            * ‖(Chain.freeSub q (Chain.chain q W A₀ ξ k ω).2).starProjection (ξ k ω)‖ ^ 2
          + ChainWiring.chainErr q W A₀ ξ k ω := by
  intro k hk ω hω
  exact Discharge.hpt_step (hinv k hk ω hω)
    (StepInputs2.opNorm_step_le_of_stepGood hω.2 hk _) hδ hδ0 hδ1

end Hpt

/-! ## 3. H3 in the chain's own notation -/

section H3

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {ι : Type*} [DecidableEq ι] {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι}
  {A₀ : EuclideanSpace ℝ (UT n)}

/-- **H3 at the chain**: `E[‖π_k(√h · ξ_k)‖² | ℱ_k] = h · N_k`, with `N_k = Chain.freeDim`.
`StepGlue.condExp_norm_sq_starProjection_smul_random` is the same statement for an abstract random
subspace; here the subspace is the chain's own free subspace, so the right-hand side is literally
`r² · freeDim`. -/
theorem condExp_norm_sq_freeSub {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)} (k : ℕ) (r : ℝ)
    (hξm : Measurable[mΩ] (ξ k))
    (hlaw : P.map (ξ k) = stdGaussian (EuclideanSpace ℝ (UT n)))
    (hintprod : ∀ p s : UT n, Integrable (fun ω => (r • ξ k ω) p * (r • ξ k ω) s) P)
    (hint : ∀ p s : UT n, Integrable (fun ω =>
      ((Chain.freeSub q (Chain.chain q W A₀ ξ k ω).2).starProjection
          (EuclideanSpace.single p (1 : ℝ))) s * ((r • ξ k ω) p * (r • ξ k ω) s)) P)
    {ℱ : MeasurableSpace Ω} (hℱ : ℱ ≤ mΩ) [SigmaFinite (P.trim hℱ)]
    (hM : ∀ p s : UT n, StronglyMeasurable[ℱ]
      fun ω => ((Chain.freeSub q (Chain.chain q W A₀ ξ k ω).2).starProjection
        (EuclideanSpace.single p (1 : ℝ))) s)
    (hind : Indep (MeasurableSpace.comap (fun ω => r • ξ k ω) inferInstance) ℱ P) :
    P[fun ω => ‖(Chain.freeSub q (Chain.chain q W A₀ ξ k ω).2).starProjection (r • ξ k ω)‖ ^ 2 | ℱ]
      =ᵐ[P] fun ω => r ^ 2 * ((Chain.freeDim q W A₀ ξ k ω : ℕ) : ℝ) :=
  StepGlue.condExp_norm_sq_starProjection_smul_random (mΩ := mΩ) r hξm hlaw hintprod hint hℱ hM hind

end H3

end Submission.L10.DischargeGlue

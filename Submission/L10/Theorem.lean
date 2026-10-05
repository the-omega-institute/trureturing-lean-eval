import Submission.L10.TailAtStep
import Submission.L10.ChainWalk
import Submission.L10.StateInvariant4
import Submission.L10.ContactIntegrated

/-!
# Gate L-10 (`klartag_packing`) — the final statement

Brief 46.  Everything from the chain's output to the challenge statement is proved, across
reports 3, 7, 11, 13, 17, 25, 27, 31, 33, 39, 41 and 44; this module states the endpoint and names
what still feeds it.

## The statement

`klartag_packing_of_chain` has **the challenge's conclusion verbatim** — checked against
`Challenge.lean` by a `pp.all` diff (identical, 72,101 characters) and by the retyped-statement
test.  Its single hypothesis is `ChainDelivers`: for every dimension at or above
`Threshold2.n₁ = 2,073,600`, a prime, a `ChainRaw2` and the chain's output on the good line.

Everything downstream of `ChainDelivers` is a theorem:

* `TailAtStep.lemma43_input_of_raw2` — `ChainRaw2` to `Params` (`params_of_raw2`) to
  `Threshold2.remaining_of_lemma43`;
* `Assembly.exists_phi_of_params` — `Params` plus `ChainOutput` to the challenge's `φ`;
* `Threshold.klartag_packing_of_phi` — the large-`n` branch, the small-`n` branch (the unit ball in
  the open cube), the constant `c = min c₀ c₁`, and `Scaling.klartag_of_volume_ge`'s exactness.

## What still feeds `ChainDelivers`, and what does not exist yet

`ChainWalk.chainRaw2_of_walk` produces the `ChainRaw2` from the chain with **one** probabilistic
hypothesis, `hprop` — Proposition 4.1 at every step — which is brief 45's `tail_final`
(`WalkTelescope.lean`, in flight at the time of writing).

`Assembly.ChainOutput` is the drift half.  Its route is `StateInvariant4.hpt_wired'` →
`StepInputs2.driftInputs_step_chain` → `ChainDrift.DriftInputs` →
`ContactIntegrated.logdet_bound_sum` → `Assembly.exists_mem_le_of_integral_le` →
`Assembly.volume_ge_of_logDet_le`, on `StateInvariant4.wiredGood'` at `ParamsAdopted2`'s values.
Every link of that route is proved.  What is **not** available is a probability space carrying the
driving sequence with the laws, independence, integrability and filtration that
`driftInputs_step_chain` takes as twenty hypotheses: every module in the tree, this one included,
carries `ξ` abstractly with `P.map (ξ k) = stdGaussian` as a hypothesis, and no brief has been
asked to construct it.  `ChainSetup` below names that bundle.

## The thresholds, all of them

| source | threshold |
|---|---|
| the good event's failure probability (report 25 §3.2) | `n ≥ 28` |
| `c₃ = n²`'s head-room (report 41 §2) | `n ≥ 4,893` |
| Lemma 4.3's `hJ` at `J = 3` (reports 27, 30) | `n ≥ 839` |
| **`junk_endpoint_le_three` at the adopted `h = n⁻⁹`** (report 30) | **`n ≥ 2,073,600`** |

The largest is taken: `Threshold2.n₁ = 2,073,600 = 1440²`.  Below it the unit ball in the open
cube supplies the ellipsoid and `Final.smallConst` the constant, so the threshold costs nothing.
-/

set_option linter.unusedSectionVars false

namespace Submission.L10.Theorem

open MeasureTheory Metric Submission.L10 Submission.L10.ConstructionA Submission.L10.Tiling

/-- **What the chain must deliver**, for every dimension at or above the threshold: a prime, a
`ChainRaw2` (Lemma 4.3's data, report 44's `chainRaw2_of_walk`) and, on the good line, the chain's
own output (the drift half, `Assembly.ChainOutput`). -/
def ChainDelivers (c₀ : ℝ) : Prop :=
  ∀ m : ℕ, Threshold2.n₁ ≤ m →
    ∃ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p) (Q : ChainRaw2 p (m + 1)),
      ∀ g : Fin (m + 1) → ZMod p, g ≠ 0 →
        (∀ y : Fin (m + 1) → ℤ, y ≠ 0 → ‖toE (m + 1) y‖ ≤ Q.R → y ∉ latZ p (m + 1) g) →
        Assembly.ChainOutput Q.alpha g c₀

/-- **`klartag_packing` from the chain's output.**  The conclusion is `Challenge.lean`'s statement
character for character. -/
theorem klartag_packing_of_chain {c₀ : ℝ} (hc₀ : 0 < c₀) (h : ChainDelivers c₀) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      let V := EuclideanSpace ℝ (Fin (n + 1))
      ∃ φ : V →ₗ[ℝ] V, let E := φ '' Metric.ball (0 : V) 1
        (MeasureTheory.volume E : EReal) = c * n ^ 2 ∧
        {v ∈ E | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} :=
  lemma43_input_of_raw2 hc₀ h

/-- The probabilistic bundle `StepInputs2.driftInputs_step_chain` takes and that no module in the
tree constructs: a space carrying the chain's driving sequence with its law, its independence of
the past, the integrability of the terms the conditional expectations use, and a filtration it is
adapted to.  Named here so the residual is a definition rather than a paragraph. -/
structure ChainSetup (n : ℕ) : Prop where
  exists_space :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (ξ : ℕ → Ω → EuclideanSpace ℝ (Increments.UT n)),
      (∀ k, Measurable (ξ k)) ∧
      (∀ k, P.map (ξ k) = ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Increments.UT n))) ∧
      ∃ ℱ : ℕ → MeasurableSpace Ω, Monotone ℱ ∧
        (∀ k, ProbabilityTheory.Indep (MeasurableSpace.comap (ξ k) inferInstance) (ℱ k) P)

end Submission.L10.Theorem

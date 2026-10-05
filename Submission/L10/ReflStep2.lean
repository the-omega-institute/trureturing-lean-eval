import Submission.L10.LiftBound

/-!
# Gate L-10 (`klartag_packing`), brief 38 Part 2 — `reflStep` through `chainU`/`past`

Report 36 §2 reported the past-factorisation bridge for `StateInvariant.reflStep` as blocked at
1,000,000 heartbeats.  **The blocker was the direction of the `show`, not the unfolding.**  Stating
the goal with the *frozen* `reflStep` on the left and asking Lean to unfold it diverges; defining
`reflStep2` here through `chainU`/`past`, stating the bridge with the *fresh* definition on the
left, and reaching the frozen one by a single delta step at the end compiles in 14 s.  No change to
`StateInvariant.lean` is needed after all.

The three bridge lemmas below are what the fourth half-law needs.  Assembling it on top still
fails, and for the same underlying reason in a new place: `rw` with an equation *between named
definitions* (`reflStep = reflStep2`) has to match `reflStep` inside `Measurable (…)` and then check
the motive, which drags the instance back in and times out.  See the report, §4.
-/

set_option linter.unusedSectionVars false

namespace Submission.L10.ReflStep2

open MeasureTheory ProbabilityTheory Matrix Finset Module
open scoped ENNReal NNReal RealInnerProductSpace
open Submission.L10 Submission.L10.Increments Submission.L10.StateInvariant
open Submission.L10.StateInvariant2 Submission.L10.StateInvariant3

noncomputable section

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

/-- The reflected step, *defined* through the past. -/
def reflStep2 (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι) (A₀ : EuclideanSpace ℝ (UT n))
    (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (k : ℕ) (ω : Ω) : EuclideanSpace ℝ (UT n) :=
  reflOf q (chainU q W A₀ k (past ξ k ω)).2 (ξ k ω)

/-- **The bridge.**  Fresh definition on the left; the frozen `reflStep` is one delta step away. -/
theorem reflStep2_eq_reflStep (k : ℕ) (ω : Ω) :
    reflStep2 q W A₀ ξ k ω = StateInvariant.reflStep q W A₀ ξ k ω := by
  show (Chain.freeSub q (chainU q W A₀ k (past ξ k ω)).2).reflection (ξ k ω)
      = (Chain.freeSub q (Chain.chain q W A₀ ξ k ω).2).reflection (ξ k ω)
  exact reflection_congr (by rw [chain_eq_chainU]) _

/-- The same at an index `j < k`, against the past truncated at `k`. -/
theorem reflOf_past_eq_reflStep {j k : ℕ} (hjk : j < k) (ω : Ω) :
    reflOf q (chainU q W A₀ j (past ξ k ω)).2 ((past ξ k ω) j)
      = StateInvariant.reflStep q W A₀ ξ j ω := by
  have hv : (past ξ k ω) j = ξ j ω := by simp [past, hjk]
  have hchain : chainU q W A₀ j (past ξ k ω) = Chain.chain q W A₀ ξ j ω :=
    (chain_congr j fun i hi => by simp [past, lt_trans hi hjk]).symm
  rw [hv]
  show (Chain.freeSub q (chainU q W A₀ j (past ξ k ω)).2).reflection (ξ j ω)
      = (Chain.freeSub q (Chain.chain q W A₀ ξ j ω).2).reflection (ξ j ω)
  exact reflection_congr (by rw [hchain]) _

end

end Submission.L10.ReflStep2

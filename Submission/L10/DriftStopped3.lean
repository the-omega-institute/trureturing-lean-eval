import Submission.L10.DriftStopped2
import Submission.L10.PaddedLawSetup
import Submission.L10.Theorem

/-!
# Gate L-10 (`klartag_packing`) — the two sides meet

Brief 55.  `PaddedLawSetup.tailSide_on_setup` delivers the `ChainRaw2` datum at every dimension;
the drift side must deliver `Assembly.ChainOutput` for it.  This module states the drift side in
the shape that composes — quantified over the lattice scale and radius, so it fits **whatever**
`ChainRaw2` the tail side produces — and proves that the two together give
`Theorem.ChainDelivers`, hence the challenge statement.

## Why `DriftSide` is quantified over `α` and `R`

`Theorem.ChainDelivers` reads `∃ Q, ∀ g, … → ChainOutput Q.alpha g c₀`: the drift's output must be
for the *same* `Q` the tail side chose.  `PaddedLawSetup.TailSide` produces `Nonempty (ChainRaw2 …)`
and nothing more, so the drift side cannot be stated for a particular `α`.  Quantifying it over
`α` and `R` is what lets `chainDelivers_of_sides` apply it at `Q.alpha` and `Q.R` — and it is no
weakening, since the chain's drift never reads the lattice.

## What is still open

`DriftSide` itself.  Reports 49, 51 and 53 built its route — the stopped chain, its pointwise
one-step inequality, `errCond`, the bound on `‖V k‖`, the error's integrand at the disagreeing step
— and report 53 §3 names what is left: the maximal inequality (brief 54), then
`integral_stoppedErr_le`, the integrability fields, `drift_bound_stopped` and the existence step.
`MaximalHyp` below is brief 54's statement, named so the threading can be written against it.
-/

set_option linter.unusedSectionVars false

namespace Submission.L10.DriftStopped3

open MeasureTheory Matrix Finset Module Submission.L10 Submission.L10.Increments
open Submission.L10.ConstructionA Submission.L10.Tiling
open scoped RealInnerProductSpace

/-! ## 1. The drift side, and the composition -/

/-- **The drift side of `ChainDelivers`.**  For every dimension at or above the threshold, and for
every lattice scale and radius, the chain's output on a good line. -/
def DriftSide (c₀ : ℝ) : Prop :=
  ∀ m : ℕ, Threshold2.n₁ ≤ m → ∀ (p : ℕ) (α R : ℝ) (g : Fin (m + 1) → ZMod p), g ≠ 0 →
    (∀ y : Fin (m + 1) → ℤ, y ≠ 0 → ‖toE (m + 1) y‖ ≤ R → y ∉ latZ p (m + 1) g) →
    Assembly.ChainOutput α g c₀

/-- **The two halves meet.**  `PaddedLawSetup.TailSide` supplies the `ChainRaw2`; `DriftSide`
supplies the output on it. -/
theorem chainDelivers_of_sides {c₀ : ℝ} (htail : PaddedLawSetup.TailSide)
    (hdrift : DriftSide c₀) : Theorem.ChainDelivers c₀ := by
  intro m hm
  obtain ⟨p, hp, hp0, hQ⟩ := htail m hm
  obtain ⟨Q⟩ := hQ
  exact ⟨p, hp, hp0, Q, fun g hg hfree => hdrift m hm p Q.alpha Q.R g hg hfree⟩

/-- **`klartag_packing` from the two sides** — the challenge statement, character for character. -/
theorem klartag_packing_of_sides {c₀ : ℝ} (hc₀ : 0 < c₀) (htail : PaddedLawSetup.TailSide)
    (hdrift : DriftSide c₀) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      let V := EuclideanSpace ℝ (Fin (n + 1))
      ∃ φ : V →ₗ[ℝ] V, let E := φ '' Metric.ball (0 : V) 1
        (MeasureTheory.volume E : EReal) = c * n ^ 2 ∧
        {v ∈ E | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} :=
  Theorem.klartag_packing_of_chain hc₀ (chainDelivers_of_sides htail hdrift)

/-! ## 2. Brief 54's input, named -/

section Maximal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {n : ℕ}

/-- **The maximal inequality brief 54 delivers**, in the form the error estimate consumes: a
single increment read at a *random* index integrates to at most `B`.  Brief 54's
`E[‖ξ_{τ−1}‖] ≤ E[max_{k<N}‖ξ_k‖]` is exactly this, with `B` the expected maximum.

Report 53 §3 measured why the naive route fails: a Cauchy–Schwarz over the `N` disjoint events
`{τ = k+1}` costs `√N` and yields `√n·√(log n)`, which is not `o(1)`.  The pathwise bound is
`≲ c·√(dim + log N)`, which at the adopted `h = n⁻⁹` is `≈ n^{−3.5}` and makes the error total
`n^{−3}`. -/
def MaximalHyp (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (P : Measure Ω) (N : ℕ) (B : ℝ) : Prop :=
  ∀ f : Ω → ℕ, (∀ ω, f ω < N) → Integrable (fun ω => ‖ξ (f ω) ω‖) P →
    ∫ ω, ‖ξ (f ω) ω‖ ∂P ≤ B

/-- The stopped chain reads its increment at `τ − 1`, a random index below the horizon; that is
the instance of `MaximalHyp` the middle case of `stoppedErr` needs. -/
theorem integral_norm_at_tau_le {ι : Type*} [DecidableEq ι] [Countable ι]
    {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
    {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)} {η r₀ c₃ : ℝ} {N : ℕ} {B : ℝ}
    (hmax : MaximalHyp ξ P N B) (hN : 1 ≤ N)
    (hint : Integrable (fun ω => ‖ξ (StoppedChain.tau q W A₀ ξ η r₀ c₃ N ω - 1) ω‖) P) :
    ∫ ω, ‖ξ (StoppedChain.tau q W A₀ ξ η r₀ c₃ N ω - 1) ω‖ ∂P ≤ B := by
  refine hmax (fun ω => StoppedChain.tau q W A₀ ξ η r₀ c₃ N ω - 1) (fun ω => ?_) hint
  have := StoppedChain.tau_le (q := q) (W := W) (A₀ := A₀) (ξ := ξ)
    (η := η) (r₀ := r₀) (c₃ := c₃) (N := N) ω
  omega

end Maximal

end Submission.L10.DriftStopped3

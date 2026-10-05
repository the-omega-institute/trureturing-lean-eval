import Submission.L10.Theorem2R4
import Submission.L10.GoodPathBounds
import Submission.L10.FinalDischarge

/-!
# Gate L-10 (`klartag_packing`) — the challenge from the **state triple**, bypassing `GoodPathAt2`

Two facts found while preparing brief 90 step (c).

**1. `GoodPathAt2`'s count index is out of reach.**  `GoodPathLightR2.GoodPathAt2` asks for
`ω ∈ StateInvariant4.wiredGood' … N … c₃`, whose `countGood` component is at the **horizon** `N`.
The tail side bounds `P.real {y ∈ C_k}` only for `k < N` — `ChainWalkRW2.hsteps_of_walkRW2` (`:33`)
is stated for `k < numStepsAdopted2 n`, and `TailAtStepR5W2.terminal_le_wProfT` (`:92`) is pinned at
`k = N − 1`, which is why `both_sums_windowR2`'s second sum is at `N − 1`.  `|C_k|` only grows, so a
bound at `N − 1` does **not** bound `|C_N|`: the `countGood … N` component cannot be supplied.

**2. It does not have to be.**  `Theorem2R4.StateSupplyAdoptedR3` (`:124`) asks for the **state
triple** directly, and `GoodPathBounds.stateTriple_of_cut` (`:1128`) produces exactly that shape,
from `goodCut … K` — whose count is read at `K`, not at `N`.  At `K = N − 1` the drift horizon is
`N − 1` too, so the loss is one step out of `N = ⌈16 n⁷ log n⌉`: `(1/N)·2c·4·log n ≈ 58/N`, which
is nothing.  (Report `82a-hinge.md`'s rejected proposal was `K = ⌊N/2⌋`; the price it was killed for
is `(1 − K/N)`-proportional and vanishes here.)

So step (c) targets `StateSupplyAdoptedR3`, and `klartag_packing_of_stateSupplyR3` below is the
closing line — `Theorem2R4.klartag_packing_of_lightGoodPath3` with its first step dropped.

`Theorem2R4.lean` and `GoodPathBounds.lean` are reported and are not edited.
-/

set_option linter.unusedSectionVars false

namespace Submission.L10.StateSupplyBypass

open MeasureTheory Matrix Finset Module Submission.L10 Submission.L10.Increments
open Submission.L10.Theorem2R4 Submission.L10.RawDataInst2
open Submission.L10.ConstructionA Submission.L10.Tiling Submission.L10.FinalDischarge
open scoped ENNReal NNReal RealInnerProductSpace

/-- **The challenge statement from the state supply**, with `LightGoodPath3` and `GoodPathAt2` out
of the path.  `c3clamp` is `DriftStopped6c.c3Adopted''` above the threshold and `0` below, which is
what the unrestricted admissibility binders want (`c3clamp_eq` collapses it wherever it is used). -/
theorem klartag_packing_of_stateSupplyR3 {A B : ℝ} (hA : 0 < A) (hB : 0 ≤ B) {C' : ℝ}
    (h : StateSupplyAdoptedR3 A B c3clamp C') :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      let V := EuclideanSpace ℝ (Fin (n + 1))
      ∃ φ : V →ₗ[ℝ] V, let E := φ '' Metric.ball (0 : V) 1
        (MeasureTheory.volume E : EReal) = c * n ^ 2 ∧
        {v ∈ E | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} := by
  obtain ⟨c₀, hc₀, hd⟩ :=
    driftSideW3_of_stateSupplyR3 c3clamp_nonneg c3clamp_eta_le h
  exact klartag_packing_of_chain'R3 hc₀ hA hB (chainDelivers'R3_of_driftSideW3 hd)

/-- **`StateSupplyAdoptedR3` from the cut state triple.**  `GoodPathBounds.stateTriple_of_cut` is
general in `q W A₀`, so it instantiates at `windowOfR2` directly; the chain data comes from
`FinalDischarge.kSet_A0C_win`/`hq_win`/`hne_win`, which need only `0 < α` and `3 ≤ m+1`.  What is
left is the per-line bundle `hline` — brief 93's error budget, the count bound at `K`, `hS`, and
the two numeric facts. -/
theorem stateSupplyR3_of_cut {A B C' : ℝ} {K : ℕ → ℕ}
    (hK : ∀ m, K m < ParamsAdopted2.numStepsAdopted2 (m + 1))
    (hline : ∀ m : ℕ, Threshold2.n₁ ≤ m → ∀ (p : ℕ) (α : ℝ), 0 < α →
      ∀ g : Fin (m + 1) → ZMod p,
      ∃ ε S pcnt : ℝ, 0 ≤ ε ∧
        (∀ ω, ∀ k, |ChainWiring.chainErr (qC α) (DriftStopped8R5.windowOfR2 α p m g)
          (A0C (m + 1)) (ChainSetup.step (Submission.L10.cAdopted (m + 1))) k ω| ≤ ε) ∧
        (S ≤ ∑ k ∈ Finset.range (K m), ∫ ω,
          DriftStopped6.stoppedFreeDim (qC α) (DriftStopped8R5.windowOfR2 α p m g) (A0C (m + 1))
            (ChainSetup.step (Submission.L10.cAdopted (m + 1)))
            (DriftStopped6.etaAdopted (m + 1)) (DriftStopped6.r0Adopted (m + 1))
            (DriftStopped6c.c3Adopted'' (m + 1)) (ParamsAdopted2.numStepsAdopted2 (m + 1)) k ω
          ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT (m + 1))))) ∧
        ((ChainSetup.gaussPath (EuclideanSpace ℝ (UT (m + 1)))).real
          (StateInvariant4.countGood (qC α) (DriftStopped8R5.windowOfR2 α p m g) (A0C (m + 1))
            (ChainSetup.step (Submission.L10.cAdopted (m + 1))) (K m)
            (DriftStopped6c.c3Adopted'' (m + 1)))ᶜ ≤ pcnt) ∧
        GoodPathBounds.logDetLow (m + 1) (DriftStopped6c.c3Adopted'' (m + 1))
          < C' - 4 * Real.log ((m + 1 : ℕ) : ℝ) ∧
        (GoodPathBounds.driftRHS (m + 1) (A0C (m + 1))
              (DriftStopped6c.c3Adopted'' (m + 1)) ε S
            - GoodPathBounds.logDetLow (m + 1) (DriftStopped6c.c3Adopted'' (m + 1)))
            / ((C' - 4 * Real.log ((m + 1 : ℕ) : ℝ))
              - GoodPathBounds.logDetLow (m + 1) (DriftStopped6c.c3Adopted'' (m + 1)))
          + GoodPathBounds.failTotal (m + 1) pcnt < 1) :
    StateSupplyAdoptedR3 A B c3clamp C' := by
  intro m hm p hp hp0 α hα hn hraw hnd _hcov g hg _hfree _hlight
  have hm1 : 2073600 ≤ m + 1 := by
    have h2 : 2073600 ≤ m := by simpa [Threshold2.n₁] using hm
    omega
  obtain ⟨ε, S, pcnt, hε, hbdabs, hS, hcnt, hLb, hbudget⟩ := hline m hm p α hα g
  have hclamp : c3clamp (m + 1) = DriftStopped6c.c3Adopted'' (m + 1) := c3clamp_eq hm1
  rw [hclamp]
  exact GoodPathBounds.stateTriple_of_cut (q := qC α)
    (W := DriftStopped8R5.windowOfR2 α p m g) (A₀ := A0C (m + 1)) (r := 1)
    hm1 one_pos (hK m) (DriftStopped6c.c3Adopted''_nonneg (m + 1))
    (DriftStopped6c.c3Adopted''_eta_le hm1)
    (kSet_A0C_win hα hn) (hq_win hα hn) (hne_win hα hn)
    (StateSupply.symMat_A0C (m + 1)) hε hbdabs hS hcnt hLb hbudget

end Submission.L10.StateSupplyBypass

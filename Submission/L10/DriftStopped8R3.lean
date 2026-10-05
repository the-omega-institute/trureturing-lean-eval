import Submission.L10.DriftStopped8R
import Submission.L10.DriftStopped8R2

/-!
# Gate L-10 — the drift side and state supply, families indexed by `p`

Brief 83.  Report 81 §5: `ThetaTight.thetaTight p n C = 4(p−1)·n·κ_n·C/(pⁿ−1)` depends on `p`, so
the `(dimension, scale)` indexing of report 73b's `DriftSideW` and `StateSupplyAdoptedR` cannot
receive it.  `DriftSideW'` and `StateSupplyAdoptedR'` below are those two predicates with
`w : ∀ p m, ℝ → …` and `θ : ℕ → ℕ → ℝ → ℝ≥0∞`; the proof is 73b's, re-run.

`DriftStopped8R`'s `windowOfR`, `BandHypR`, `bandSideAdoptedR` and `avoid_of_casesR` are reused
unchanged — the band is still closed, and `bandSideAdoptedR` still carries the `0 < α` that report
73b §1 showed is necessary.
-/

set_option linter.unusedSectionVars false

namespace Submission.L10.DriftStopped8R3

open MeasureTheory Matrix Finset Module Submission.L10 Submission.L10.Increments
open Submission.L10.ConstructionA Submission.L10.Tiling Submission.L10.PaddedLawSetup
open Submission.L10.TailSideSetup2 Submission.L10.RawDataInst2 Submission.L10.Theorem2
open Submission.L10.DriftStopped7 Submission.L10.DriftStopped8
open Submission.L10.PaddedLawSetupR Submission.L10.RawDataInst2R
open Submission.L10.LatticeDataR Submission.L10.WindowR
open Submission.L10.DriftStopped8R Submission.L10.Theorem4R2
open scoped ENNReal RealInnerProductSpace

/-- **`DriftStopped8R.DriftSideW` with both families indexed by `p`.** -/
def DriftSideW' (w : ∀ _p m : ℕ, ℝ → (Fin (m + 1) → ℤ) → ℝ≥0∞) (θ : ℕ → ℕ → ℝ → ℝ≥0∞)
    (c₀ : ℝ) : Prop :=
  ∀ m : ℕ, Threshold2.n₁ ≤ m → ∀ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p) (α : ℝ),
    0 < α → ∀ (_hn : 3 ≤ m + 1)
      (_hraw : RawDataR p (m + 1) α ((1 - 1 / ((m + 1 : ℕ) : ℝ)) / α)
        (qC α) (shellR α (m + 1)) (A0C (m + 1)))
      (_hnd : NormData (m + 1) α (qC α) (shellR α (m + 1)) (A0C (m + 1))),
      (∀ y : Fin (m + 1) → ℤ, y ≠ 0 →
        (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α < ‖toE (m + 1) y‖ →
        ‖toE (m + 1) y‖ + Real.sqrt ((m + 1 : ℕ) : ℝ) / 2 ≤ windowR α (m + 1) →
          y ∈ shellR α (m + 1)) →
      ∀ (g : Fin (m + 1) → ZMod p), g ≠ 0 →
      (∀ y : Fin (m + 1) → ℤ, y ≠ 0 →
        ‖toE (m + 1) y‖ ≤ (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α → y ∉ latZ p (m + 1) g) →
      LightContact (w p m α) (shellR α (m + 1)) (θ p m α) g →
      Assembly.ChainOutput α g c₀

/-- **`DriftStopped8R.StateSupplyAdoptedR` with both families indexed by `p`.**  This is the
statement brief 82b's `hgood'` must produce. -/
def StateSupplyAdoptedR' (w : ∀ _p m : ℕ, ℝ → (Fin (m + 1) → ℤ) → ℝ≥0∞) (θ : ℕ → ℕ → ℝ → ℝ≥0∞)
    (C' : ℝ) : Prop :=
  ∀ m : ℕ, Threshold2.n₁ ≤ m → ∀ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p) (α : ℝ),
    0 < α → ∀ (_hn : 3 ≤ m + 1)
      (_hraw : RawDataR p (m + 1) α ((1 - 1 / ((m + 1 : ℕ) : ℝ)) / α)
        (qC α) (shellR α (m + 1)) (A0C (m + 1)))
      (_hnd : NormData (m + 1) α (qC α) (shellR α (m + 1)) (A0C (m + 1))),
      (∀ y : Fin (m + 1) → ℤ, y ≠ 0 →
        (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α < ‖toE (m + 1) y‖ →
        ‖toE (m + 1) y‖ + Real.sqrt ((m + 1 : ℕ) : ℝ) / 2 ≤ windowR α (m + 1) →
          y ∈ shellR α (m + 1)) →
      ∀ (g : Fin (m + 1) → ZMod p), g ≠ 0 →
      (∀ y : Fin (m + 1) → ℤ, y ≠ 0 →
        ‖toE (m + 1) y‖ ≤ (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α → y ∉ latZ p (m + 1) g) →
      LightContact (w p m α) (shellR α (m + 1)) (θ p m α) g →
      ∃ (A : EuclideanSpace ℝ (UT (m + 1))) (M : ℝ),
        A ∈ Chain.kSet (qC α) (windowOfR α p m g) ∧
        Discharge.StateBounds (symMat A) (DriftStopped6.mAdopted (m + 1)) M ∧
        ChainWiring.logDet A ≤ C' - 4 * Real.log ((m + 1 : ℕ) : ℝ)

/-- **Goal (5) at the reach window, `p`-indexed.**  Report 73b's proof, re-run: the band is
`bandSideAdoptedR`, the avoidance `avoid_of_casesR`, and `c₀ = exp(−C'/2)` is produced. -/
theorem driftSide'''''_of_stateSupplyR'
    {w : ∀ _p m : ℕ, ℝ → (Fin (m + 1) → ℤ) → ℝ≥0∞} {θ : ℕ → ℕ → ℝ → ℝ≥0∞} {C' : ℝ}
    (h : StateSupplyAdoptedR' w θ C') :
    ∃ c₀ : ℝ, 0 < c₀ ∧ DriftSideW' w θ c₀ := by
  refine ⟨Real.exp (-C' / 2), Real.exp_pos _, ?_⟩
  intro m hm p hp hp0 α hα hn hraw hnd hcov g hg hfree hlight
  obtain ⟨A, M, hkSet, hSB, hlog⟩ := h m hm p hp hp0 α hα hn hraw hnd hcov g hg hfree hlight
  have hm0 : m ≠ 0 := by
    have h2 : 2073600 ≤ m := by simpa [Threshold2.n₁] using hm
    omega
  exact chainOutput_of_state hm0 hSB hlog
    (avoid_of_casesR hα hSB hkSet hcov hfree (bandSideAdoptedR m hm p α hα g))

end Submission.L10.DriftStopped8R3

/-
Gate L-10 (`klartag_packing`), brief 95 — the six tail-side hypotheses of
`TailAtStepR5W2.both_sums_windowR2`, at `windowOfR2`.

Five are geometric and come from `RawDataInst2RW2.lattice_fieldsR` through
`DriftStopped8R5.windowOfR2_subset`, in the pattern `FinalDischarge.hq_win` already uses.  The
sixth, `hprop`, is the constraint process's tail; it is **not** a quantifier restriction, because
`constraintM q W A₀ ξ` depends on `W`.  It is **already a theorem**:
`TailSideSetup3W2.tailSideHyp_latZR'`, since `windowOfR2` is by definition
`shellR.filter (· ∈ latZ p n g)`.

**A correction to my own report 95-status, recorded here so it is not repeated.**  I first read
the docstrings of `RawDataInst2RW2.hole52R_of_tailSideHyp` and `LatticeDataRW2.tailSideHyp_filterR`
— both say the producer is missing because `TailSideSetup2.tailSideHyp_of_rawData` wants a
`windowC`-shaped `RawData` — and rebuilt the window-free restatement, believing HOLE 52 open.
Those docstrings are **stale**.  `TailSideSetup3W2` closed it: `tailSideHyp_of_gap` is the
window-free restatement, `tailSideHyp_of_rawDataR` the reach-lane producer, `tailSideHyp_latZR'`
the lattice-filtered form, and `hole52R` the hypothesis-free statement.  My duplicate is deleted.
The search error was mine: I grepped for a conclusion `: TailSideHypR`, and these state the
conclusion on its own indented line, so the pattern never matched.

Nothing reported is edited.
-/
import Submission.L10.TailSideSetup3W2
import Submission.L10.FinalDischarge

set_option linter.unusedSectionVars false

namespace Submission.L10.TailHypsWindow

open MeasureTheory Matrix Finset Module Submission.L10 Submission.L10.Increments
open Submission.L10.ChainSetup Submission.L10.ConstructionA Submission.L10.Tiling
open Submission.L10.PaddedLawSetup Submission.L10.PaddedLawSetupRW2
open Submission.L10.RawDataInst2RW2 Submission.L10.RawDataInst2
open Submission.L10.DriftStopped8R5 Submission.L10.TailSideSetup2 Submission.L10.WindowR2
open scoped ENNReal NNReal RealInnerProductSpace

variable {p m : ℕ} {α R : ℝ} {g : Fin (m + 1) → ZMod p}

/-! ## 1. The five geometric hypotheses -/

theorem hq_j_win (hα : 0 < α) (hn : 3 ≤ m + 1) :
    ∀ j : (Fin (m + 1) → ℤ), ∀ i ∈ windowOfR2 α p m g, (0 : ℝ) ≤ ⟪qC α i, qC α j⟫ :=
  fun j i hi => (lattice_fieldsR hα hn).1 j i (windowOfR2_subset hi)

theorem hA₀_win (hα : 0 < α) (hn : 3 ≤ m + 1) :
    ∀ y ∈ windowOfR2 α p m g, (1 : ℝ) < ⟪A0C (m + 1), qC α y⟫ :=
  fun y hy => (lattice_fieldsR hα hn).2.1 y (windowOfR2_subset hy)

theorem hwin_win (hα : 0 < α) (hn : 3 ≤ m + 1) :
    ∀ y ∈ windowOfR2 α p m g,
      ‖toE (m + 1) y‖ + Real.sqrt ((m + 1 : ℕ) : ℝ) / 2 ≤ windowR2 α (m + 1) :=
  fun y hy => (lattice_fieldsR hα hn).2.2.2.2.1 y (windowOfR2_subset hy)

theorem hr_win (hα : 0 < α) (hn : 3 ≤ m + 1) :
    ∀ y ∈ windowOfR2 α p m g, 0 < α * ‖toE (m + 1) y‖ :=
  fun y hy => (lattice_fieldsR hα hn).2.2.2.2.2.1 y (windowOfR2_subset hy)

theorem hy_win (hα : 0 < α) (hn : 3 ≤ m + 1) :
    ∀ k, k < ParamsAdopted2.numStepsAdopted2 (m + 1) → k ≠ 0 →
      ∀ y ∈ windowOfR2 α p m g,
        0 < yOf (a0C (m + 1)) ((k : ℝ) * ParamsAdopted2.stepSizeAdopted2 (m + 1))
          (α * ‖toE (m + 1) y‖) :=
  fun k hk hk0 y hy =>
    (lattice_fieldsR hα hn).2.2.2.2.2.2 k hk hk0 y (windowOfR2_subset hy)

/-! ## 2. `hprop`, from the closed hole -/

/-- **The constraint process's tail at the window**, named in the argument order
`both_sums_windowR2` reads.  This is `TailSideSetup3W2.tailSideHyp_latZR'` at `W := shellR`, since
`windowOfR2 α p m g = (shellR α (m+1)).filter (· ∈ latZ p (m+1) g)` definitionally. -/
theorem hprop_win
    (hraw : RawDataR p (m + 1) α R (qC α) (RawDataInst2RW2.shellR α (m + 1)) (A0C (m + 1)))
    (hnd : NormData (m + 1) α (qC α) (RawDataInst2RW2.shellR α (m + 1)) (A0C (m + 1)))
    (hn : 3 ≤ m + 1) :
    ∀ k, k < ParamsAdopted2.numStepsAdopted2 (m + 1) → k ≠ 0 →
      ∀ y ∈ windowOfR2 α p m g,
        (ChainSetup.gaussPath (EuclideanSpace ℝ (UT (m + 1))))
            {ω | ∃ i ≤ k, constraintM (qC α) (windowOfR2 α p m g) (A0C (m + 1))
              (ChainSetup.step (Real.sqrt (ParamsAdopted2.stepSizeAdopted2 (m + 1)))) y i ω ≤ 0}
          ≤ ENNReal.ofReal (4 * Phi (yOf (a0C (m + 1))
              ((k : ℝ) * ParamsAdopted2.stepSizeAdopted2 (m + 1))
              (α * ‖toE (m + 1) y‖))) :=
  TailSideSetup3W2.tailSideHyp_latZR' hraw hnd hn g

/-- The same at the chain's own scale name, `Submission.L10.cAdopted (m+1) = √h`. -/
theorem cAdopted_eq_sqrt :
    Submission.L10.cAdopted (m + 1)
      = Real.sqrt (ParamsAdopted2.stepSizeAdopted2 (m + 1)) := rfl

end Submission.L10.TailHypsWindow

import Submission.L10.TailAtStepR3W2
import Submission.L10.Lemma43UniformR2

/-!
# Gate L-10 (`klartag_packing`), brief 85d — the `windowR2` fold-in, hypothesis-free

Report 85b §5 named two upstream theorems.  Brief 85a supplied the first:
`Lemma43R2.radial_bound4_of_chain2` (`:310`) is stated **at `WindowR2.windowR2`** and its
right-hand side is `TailAtStepR2W2.fR4`, with the **same** constant `4·C1R α n·(8 − 8/n²)` as the
`windowR` lane — so `Lemma43R.C4_pos` still supplies positivity.  Two `exact`s make
`TailAtStepR3W2.paramsProducerR2'_of_radial` hypothesis-free.

`TailAtStepR3W2` is reported (report 85b), so this is a new module rather than an edit.
-/

set_option linter.unusedSectionVars false

namespace Submission.L10.TailAtStepR4W2

open MeasureTheory Set Real Finset
open scoped ENNReal NNReal
open Submission.L10 Submission.L10.Increments Submission.L10.ChainDataInst
open Submission.L10.Tiling Submission.L10.Section5 Submission.L10.ConstructionA
open Submission.L10.WindowR2 Submission.L10.TailAtStepR2W2

noncomputable section

/-- Lemma 4.3's constant at the reach-2 window — the same one as at `windowR`. -/
def CR2 (m : ℕ) (α : ℝ) : ℝ :=
  4 * Lemma43R.C1R α (m + 1) * (8 - 8 / ((m + 1 : ℕ) : ℝ) ^ 2)

/-- The tight threshold family at that constant. -/
def thetaR2 (p m : ℕ) (α : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (ThetaTight.thetaTight p (m + 1) (CR2 m α))

/-- **The `windowR2` producer, with no hypothesis.**  The two `exact`s of brief 85d. -/
theorem paramsProducerR2'_tight :
    ∀ (p m : ℕ) (_ : Fact (Nat.Prime p)), 2073600 ≤ m + 1 → ∀ Q : ChainRaw2RW2 p (m + 1),
      ∃ P : Params p (m + 1), P.alpha = Q.alpha ∧ P.R = Q.R ∧ P.supp = Q.supp ∧
        P.w = Q.w ∧ P.theta = thetaR2 p m Q.alpha := by
  intro p m _hp hm Q
  have hα : 0 < Q.alpha := Q.alpha_pos
  have hC : 0 < CR2 m Q.alpha := Lemma43R.C4_pos hm hα
  have hrad : ∫ y in Ioi (0 : ℝ), y ^ (m + 1 - 1) * fR4 Q.alpha (m + 1) y ≤ CR2 m Q.alpha :=
    Lemma43R2.radial_bound4_of_chain2 hm hα Q.tiling_defect
  exact ⟨params_of_raw2R_of_radial hm Q hC hrad, params_fields hm Q hC hrad⟩

end

end Submission.L10.TailAtStepR4W2

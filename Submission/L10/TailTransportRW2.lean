import Submission.L10.TailTransport
import Submission.L10.TailAtStepRW2

/-!
# Gate L-10 (`klartag_packing`), brief 72 — `TailTransport` at the reach window

The two `windowC`-naming declarations of `TailTransport`, at `windowR2`.  `measure_hitSet_fst`,
`hit_tail_yOf`, `map_pi_of_iIndep` and `map_frozen_coord` name no window and are called.
-/

set_option linter.unusedSectionVars false

namespace Submission.L10

open MeasureTheory ProbabilityTheory Set Real Submission.L10.ChainDataInst Submission.L10.Tiling
open Submission.L10.WindowR2
open scoped ENNReal NNReal

theorem tail_at_step_μRW2 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} {α hstep : ℝ} {N : ℕ} (C : ℕ → Ω → Finset (Fin n → ℤ))
    (W : Finset (Fin n → ℤ)) (M : (Fin n → ℤ) → ℕ → Ω → ℝ)
    (hwin : ∀ y ∈ W, ‖toE n y‖ + Real.sqrt n / 2 ≤ windowR2 α n)
    (hr : ∀ y ∈ W, 0 < α * ‖toE n y‖)
    (hy : ∀ k, k < N → k ≠ 0 → ∀ y ∈ W,
      0 < yOf (a0C n) ((k : ℝ) * hstep) (α * ‖toE n y‖))
    (hhit : ∀ k, k < N → ∀ y ∈ W,
      {ω | y ∈ C k ω} ⊆ {ω | ∃ j ≤ k, M y j ω ≤ 0})
    (hprop : ∀ k, k < N → k ≠ 0 → ∀ y ∈ W,
      μ {ω | ∃ j ≤ k, M y j ω ≤ 0}
        ≤ ENNReal.ofReal (4 * Phi (yOf (a0C n) ((k : ℝ) * hstep) (α * ‖toE n y‖))))
    (hzero : ∀ y ∈ W, μ.real {ω | y ∈ C 0 ω} = 0) :
    ∀ k, k < N → ∀ y ∈ W,
      μ.real {ω | y ∈ C k ω}
        ≤ 4 * profStepRW2 α n hstep y k := by
  refine tail_at_stepRW2 C W hwin hr hy ?_ hzero
  intro k hk hk0 y hy'
  exact le_trans (measure_mono (hhit k hk y hy')) (hprop k hk hk0 y hy')

/-- The same, folded into `profStepRW2`'s definition — the literal shape `ChainRaw2RW2.tail` is proved
from, through `TailAtStep.tail_of_stepsRW2`. -/
theorem tail_of_transportRW2 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} {α : ℝ} (hn : 3 ≤ n) (hα : 0 < α)
    (C : ℕ → Ω → Finset (Fin n → ℤ)) (W : Finset (Fin n → ℤ))
    (M : (Fin n → ℤ) → ℕ → Ω → ℝ)
    (hwin : ∀ y ∈ W, ‖toE n y‖ + Real.sqrt n / 2 ≤ windowR2 α n)
    (hr : ∀ y ∈ W, 0 < α * ‖toE n y‖)
    (hy : ∀ k, k < ParamsAdopted2.numStepsAdopted2 n → k ≠ 0 → ∀ y ∈ W,
      0 < yOf (a0C n) ((k : ℝ) * ParamsAdopted2.stepSizeAdopted2 n) (α * ‖toE n y‖))
    (hhit : ∀ k, k < ParamsAdopted2.numStepsAdopted2 n → ∀ y ∈ W,
      {ω | y ∈ C k ω} ⊆ {ω | ∃ j ≤ k, M y j ω ≤ 0})
    (hprop : ∀ k, k < ParamsAdopted2.numStepsAdopted2 n → k ≠ 0 → ∀ y ∈ W,
      μ {ω | ∃ j ≤ k, M y j ω ≤ 0}
        ≤ ENNReal.ofReal (4 * Phi (yOf (a0C n)
            ((k : ℝ) * ParamsAdopted2.stepSizeAdopted2 n) (α * ‖toE n y‖))))
    (hzero : ∀ y ∈ W, μ.real {ω | y ∈ C 0 ω} = 0) :
    ∀ y ∈ W, ENNReal.ofReal (ContactIntegrated.intWeight μ C
        (ParamsAdopted2.stepSizeAdopted2 n) (ParamsAdopted2.numStepsAdopted2 n) y)
      ≤ ENNReal.ofReal (4 * ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
          profileAt (a0C n) α (windowR2 α n) n t ‖toE n y‖) :=
  fun y hy' => tail_of_stepsRW2 hn hα C
    (fun k hk => tail_at_step_μRW2 C W M hwin hr hy hhit hprop hzero k hk y hy')

end Submission.L10

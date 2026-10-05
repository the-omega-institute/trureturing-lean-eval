import Submission.L10.PaddingMap
import Submission.L10.TailTransportR

/-!
# Gate L-10 (`klartag_packing`), brief 72 — `PaddingMap` at the reach window

`PaddingMap`'s single `windowC`-naming declaration, `tail_of_transport'`, at `windowR`.  All of
the padding machinery (`map_frozen`, `indepFun_frozen`, `hincl_of_padding`, `hincl_prod`,
`contact_zero_of_gap`) names no window and is called.
-/

set_option linter.unusedSectionVars false

namespace Submission.L10

open MeasureTheory ProbabilityTheory Set Real Submission.L10.WindowR
open scoped ENNReal NNReal RealInnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem tail_of_transport'R {n : ℕ} {α : ℝ} (hn : 3 ≤ n) (hα : 0 < α)
    (C : ℕ → Ω → Finset (Fin n → ℤ)) (W : Finset (Fin n → ℤ))
    (M : (Fin n → ℤ) → ℕ → Ω → ℝ)
    (hwin : ∀ y ∈ W, ‖Tiling.toE n y‖ + Real.sqrt n / 2 ≤ windowR α n)
    (hr : ∀ y ∈ W, 0 < α * ‖Tiling.toE n y‖)
    (hy : ∀ k, k < ParamsAdopted2.numStepsAdopted2 n → k ≠ 0 → ∀ y ∈ W,
      0 < yOf (a0C n) ((k : ℝ) * ParamsAdopted2.stepSizeAdopted2 n)
        (α * ‖Tiling.toE n y‖))
    (hhit : ∀ k, k < ParamsAdopted2.numStepsAdopted2 n → ∀ y ∈ W,
      {ω | y ∈ C k ω} ⊆ {ω | ∃ j ≤ k, M y j ω ≤ 0})
    (hprop : ∀ k, k < ParamsAdopted2.numStepsAdopted2 n → k ≠ 0 → ∀ y ∈ W,
      P {ω | ∃ j ≤ k, M y j ω ≤ 0}
        ≤ ENNReal.ofReal (4 * Phi (yOf (a0C n)
            ((k : ℝ) * ParamsAdopted2.stepSizeAdopted2 n) (α * ‖Tiling.toE n y‖))))
    (hgap : ∀ y ∈ W, ∀ ω, 0 < M y 0 ω) :
    ∀ y ∈ W, ENNReal.ofReal (ContactIntegrated.intWeight P C
        (ParamsAdopted2.stepSizeAdopted2 n) (ParamsAdopted2.numStepsAdopted2 n) y)
      ≤ ENNReal.ofReal (4 * ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
          profileAt (a0C n) α (windowR α n) n t ‖Tiling.toE n y‖) :=
  tail_of_transportR hn hα C W M hwin hr hy hhit hprop
    (contact_zero_of_gap C W M
      (fun y hy' => hhit 0 (by
        have h := ChainDrift.numSteps_pos (n := n) (e := 7) hn
        have h2 : 0 < ChainDrift.numSteps n 7 := by exact_mod_cast h
        exact h2) y hy') hgap)

end Submission.L10

import Submission.L10.ChainWalk
import Submission.L10.PaddingMapRW2

/-!
# Gate L-10 (`klartag_packing`), brief 72 — `ChainWalk` at the reach window

`ChainWalk`'s four `windowC`-naming declarations, at `windowR2`.  The walk itself (`pureWalk`,
`constraintM`, `chain_hhit`, `chain_hgap`, `contactSet`) names no window and is called.

## The weight-carrying fields (route note of brief 72, 2026-09-12)

Report 62b found that the count event needs a **terminal**-count weight, distinct from the
time-integrated one that feeds the drift, and brief 74 is deciding whether `ChainRaw2`'s
`w`/`tail`/`dom`/`f`/`radial_bound`/`theta`/`markov` become one combined weight.  Until that lands,
`ChainRaw2RW2` and `chainRaw2_of_chainRW2` below carry those fields **exactly as in the originals**;
everything else (`alpha`, `R`, the tiling defect, the window at `windowR2`, `supp`,
`supp_ne_zero`, `supp_radius`, `arith`) is the verbatim copy this brief asks for.
-/

set_option linter.unusedSectionVars false

namespace Submission.L10

open MeasureTheory Set Real Submission.L10.Chain
open Submission.L10.Tiling Submission.L10.Section5 Submission.L10.ConstructionA
open Submission.L10.ChainDataInst Submission.L10.WindowR2
open scoped ENNReal RealInnerProductSpace

variable {n : ℕ} {Ωc : Type*} [MeasurableSpace Ωc] {P : Measure Ωc} [IsProbabilityMeasure P]
variable {Ec : Type*} [NormedAddCommGroup Ec] [InnerProductSpace ℝ Ec] [FiniteDimensional ℝ Ec]
variable {q : (Fin n → ℤ) → Ec} {W : Finset (Fin n → ℤ)} {A₀ : Ec} {ξ : ℕ → Ωc → Ec} {α : ℝ}

theorem hsteps_of_walkRW2
    (hq : ∀ j : (Fin n → ℤ), ∀ i ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫)
    (hA₀ : ∀ y ∈ W, (1 : ℝ) < ⟪A₀, q y⟫)
    (hwin : ∀ y ∈ W, ‖toE n y‖ + Real.sqrt n / 2 ≤ windowR2 α n)
    (hr : ∀ y ∈ W, 0 < α * ‖toE n y‖)
    (hy : ∀ k, k < ParamsAdopted2.numStepsAdopted2 n → k ≠ 0 → ∀ y ∈ W,
      0 < yOf (a0C n) ((k : ℝ) * ParamsAdopted2.stepSizeAdopted2 n) (α * ‖toE n y‖))
    (hprop : ∀ k, k < ParamsAdopted2.numStepsAdopted2 n → k ≠ 0 → ∀ y ∈ W,
      P {ω | ∃ i ≤ k, constraintM q W A₀ ξ y i ω ≤ 0}
        ≤ ENNReal.ofReal (4 * Phi (yOf (a0C n)
            ((k : ℝ) * ParamsAdopted2.stepSizeAdopted2 n) (α * ‖toE n y‖)))) :
    ∀ k, k < ParamsAdopted2.numStepsAdopted2 n → ∀ y ∈ W,
      P.real {ω | y ∈ contactSet q W A₀ ξ k ω}
        ≤ 4 * profStepRW2 α n (ParamsAdopted2.stepSizeAdopted2 n) y k :=
  tail_at_step_μRW2 (contactSet q W A₀ ξ) W (constraintM q W A₀ ξ) hwin hr hy
    (fun k _ y _ => chain_hhit hq k y) hprop
    (contact_zero_of_gap (contactSet q W A₀ ξ) W (constraintM q W A₀ ξ)
      (fun y _ => chain_hhit hq 0 y)
      (fun y hy' ω => chain_hgap (hA₀ y hy') ω))

/-- **`ChainRaw2RW2.tail` from the chain.** -/
theorem tail_of_transport''RW2 (hn : 3 ≤ n) (hα : 0 < α)
    (hq : ∀ j : (Fin n → ℤ), ∀ i ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫)
    (hA₀ : ∀ y ∈ W, (1 : ℝ) < ⟪A₀, q y⟫)
    (hwin : ∀ y ∈ W, ‖toE n y‖ + Real.sqrt n / 2 ≤ windowR2 α n)
    (hr : ∀ y ∈ W, 0 < α * ‖toE n y‖)
    (hy : ∀ k, k < ParamsAdopted2.numStepsAdopted2 n → k ≠ 0 → ∀ y ∈ W,
      0 < yOf (a0C n) ((k : ℝ) * ParamsAdopted2.stepSizeAdopted2 n) (α * ‖toE n y‖))
    (hprop : ∀ k, k < ParamsAdopted2.numStepsAdopted2 n → k ≠ 0 → ∀ y ∈ W,
      P {ω | ∃ i ≤ k, constraintM q W A₀ ξ y i ω ≤ 0}
        ≤ ENNReal.ofReal (4 * Phi (yOf (a0C n)
            ((k : ℝ) * ParamsAdopted2.stepSizeAdopted2 n) (α * ‖toE n y‖)))) :
    ∀ y ∈ W, ENNReal.ofReal (ContactIntegrated.intWeight P (contactSet q W A₀ ξ)
        (ParamsAdopted2.stepSizeAdopted2 n) (ParamsAdopted2.numStepsAdopted2 n) y)
      ≤ ENNReal.ofReal (4 * ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
          profileAt (a0C n) α (windowR2 α n) n t ‖toE n y‖) :=
  fun y hy' => tail_of_stepsRW2 hn hα (contactSet q W A₀ ξ)
    (fun k hk => hsteps_of_walkRW2 hq hA₀ hwin hr hy hprop k hk y hy')

theorem terminal_tailRW2 {N : ℕ} {hstep : ℝ}
    (hq : ∀ j : (Fin n → ℤ), ∀ i ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫)
    (hwin : ∀ y ∈ W, ‖toE n y‖ + Real.sqrt n / 2 ≤ windowR2 α n)
    (hr : ∀ y ∈ W, 0 < α * ‖toE n y‖)
    (hyN : ∀ y ∈ W, 0 < yOf (a0C n) ((N : ℝ) * hstep) (α * ‖toE n y‖))
    (hpropN : ∀ y ∈ W, P {ω | ∃ i ≤ N, constraintM q W A₀ ξ y i ω ≤ 0}
      ≤ ENNReal.ofReal (4 * Phi (yOf (a0C n) ((N : ℝ) * hstep) (α * ‖toE n y‖)))) :
    ∀ y ∈ W, P.real {ω | y ∈ contactSet q W A₀ ξ N ω}
      ≤ 4 * profileAt (a0C n) α (windowR2 α n) n ((N : ℝ) * hstep) ‖toE n y‖ := by
  intro y hy'
  rw [profileAt_eq_Phi (hwin y hy') (hr y hy') (hyN y hy')]
  refine measureReal_le_of_le (by
    have := Phi_nonneg (hyN y hy'); linarith) ?_
  exact le_trans (measure_mono (chain_hhit hq N y)) (hpropN y hy')

/-- **`ChainRaw2RW2` from the chain**, with `w = intWeight` and `tail` discharged.  The thirteen
remaining arguments are §5 arithmetic and the chain's own lattice data. -/
noncomputable def chainRaw2_of_walkRW2 {p : ℕ} (hn : 3 ≤ n)
    (hq : ∀ j : (Fin n → ℤ), ∀ i ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫)
    (hA₀ : ∀ y ∈ W, (1 : ℝ) < ⟪A₀, q y⟫)
    (alpha_pos : 0 < α)
    (alpha_norm : α ^ n * ((p ^ (n - 1) : ℕ) : ℝ) = kappa n)
    (R : ℝ) (R_nonneg : 0 ≤ R) (R_scaled : α * R ≤ 1 - 1 / (n : ℝ)) (R_lt_p : R < (p : ℝ))
    (tiling_defect : (n : ℝ) * (α * Real.sqrt n / 2) ≤ 1 / 4)
    (window_lt_p : windowR2 α n < (p : ℝ))
    (supp_ne_zero : ∀ y ∈ W, y ≠ 0)
    (supp_radius : ∀ y ∈ W, ‖toE n y‖ ≤ windowR2 α n)
    (hwin : ∀ y ∈ W, ‖toE n y‖ + Real.sqrt n / 2 ≤ windowR2 α n)
    (hr : ∀ y ∈ W, 0 < α * ‖toE n y‖)
    (hy : ∀ k, k < ParamsAdopted2.numStepsAdopted2 n → k ≠ 0 → ∀ y ∈ W,
      0 < yOf (a0C n) ((k : ℝ) * ParamsAdopted2.stepSizeAdopted2 n) (α * ‖toE n y‖))
    (hprop : ∀ k, k < ParamsAdopted2.numStepsAdopted2 n → k ≠ 0 → ∀ y ∈ W,
      P {ω | ∃ i ≤ k, constraintM q W A₀ ξ y i ω ≤ 0}
        ≤ ENNReal.ofReal (4 * Phi (yOf (a0C n)
            ((k : ℝ) * ParamsAdopted2.stepSizeAdopted2 n) (α * ‖toE n y‖))))
    (arith : (n : ℝ) * kappa n * ((p : ℝ) - 1) * (8 - 8 / (n : ℝ) ^ 2)
      < 8 * ((p : ℝ) ^ n - 1)) :
    ChainRaw2RW2 p n :=
  chainRaw2_of_chainRW2 (μ := P) hn (contactSet q W A₀ ξ) α alpha_pos alpha_norm R R_nonneg
    R_scaled R_lt_p tiling_defect window_lt_p W supp_ne_zero supp_radius
    (fun y hy' k hk => hsteps_of_walkRW2 hq hA₀ hwin hr hy hprop k hk y hy') arith

end Submission.L10

import Mathlib
import Submission.L10.Theorem4
import Submission.L10.LatticeDataR

/-!
# Gate L-10 — the drift side at the reach window

Brief 73, part 5.  `Theorem4.DriftSide'''` with `windowC → windowR`, `shell → shellR`, and the
light-contact threshold left as a parameter `θ` until brief 71's `C1R` lands; the intended
specialisation is `θ α n = ENNReal.ofReal (64 * C1R α n)`, which is `Theorem2.params_of_raw2_theta`
at the reach window.

**One binder is exposed that `DriftSide'''` hides.**  `Theorem2.chainW` builds its weight from
`TailSideSetup2.tailSideHyp_of_rawData`, which demands a `windowC`-shaped `PaddedLawSetup.RawData`;
at the reach window no such producer exists yet (see `RawDataInst2R`'s docstring — the missing piece
is a window-free restatement, since that proof reads only `hA₀` and `hr`).  So `chainWR` takes the
tail-side hypothesis as an argument and `DriftSide''''` quantifies over it.  When the restatement
lands, `htail` becomes derivable from `hraw` and `hnd` and the binder can be dropped, leaving
`DriftSide''''` textually `DriftSide'''` with the three substitutions.
-/

set_option linter.unusedSectionVars false

open MeasureTheory Finset

namespace Submission.L10.Theorem4R

open scoped ENNReal RealInnerProductSpace
open Submission.L10 Submission.L10.Increments Submission.L10.Tiling
open Submission.L10.ConstructionA Submission.L10.PaddedLawSetup
open Submission.L10.TailSideSetup2 Submission.L10.RawDataInst2 Submission.L10.Theorem2
open Submission.L10.PaddedLawSetupR Submission.L10.RawDataInst2R
open Submission.L10.LatticeDataR Submission.L10.WindowR

/-- **The chain's weight at the reach window.**  `Theorem2.chainW` with `chainRaw2_on_setupR`; the
tail-side hypothesis is an argument rather than a derived fact (see the module docstring). -/
noncomputable def chainWR {p m : ℕ} {α R c : ℝ}
    {q : (Fin (m + 1) → ℤ) → EuclideanSpace ℝ (UT (m + 1))} {W : Finset (Fin (m + 1) → ℤ)}
    {A₀ : EuclideanSpace ℝ (UT (m + 1))} (hn : 3 ≤ m + 1)
    (hdata : RawDataR p (m + 1) α R q W A₀) (htail : TailSideHypR (m + 1) c α q W A₀) :
    (Fin (m + 1) → ℤ) → ℝ≥0∞ :=
  (chainRaw2_on_setupR hn hdata htail).w

/-- **The drift side at the reach window, with coverage.**  `Theorem4.DriftSide'''` with
`windowC → windowR`, `shell → shellR`, and the light-contact threshold `θ`. -/
def DriftSide'''' (θ : ℝ → ℕ → ℝ≥0∞) (c₀ : ℝ) : Prop :=
  ∀ m : ℕ, Threshold2.n₁ ≤ m → ∀ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p) (α : ℝ),
    0 < α → ∀ (hn : 3 ≤ m + 1)
      (hraw : RawDataR p (m + 1) α ((1 - 1 / ((m + 1 : ℕ) : ℝ)) / α)
        (qC α) (shellR α (m + 1)) (A0C (m + 1)))
      (_hnd : NormData (m + 1) α (qC α) (shellR α (m + 1)) (A0C (m + 1)))
      (htail : TailSideHypR (m + 1)
        (Real.sqrt (ParamsAdopted2.stepSizeAdopted2 (m + 1))) α
        (qC α) (shellR α (m + 1)) (A0C (m + 1))),
      (∀ y : Fin (m + 1) → ℤ, y ≠ 0 →
        (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α < ‖toE (m + 1) y‖ →
        ‖toE (m + 1) y‖ + Real.sqrt ((m + 1 : ℕ) : ℝ) / 2 ≤ windowR α (m + 1) →
          y ∈ shellR α (m + 1)) →
      ∀ (g : Fin (m + 1) → ZMod p), g ≠ 0 →
      (∀ y : Fin (m + 1) → ℤ, y ≠ 0 →
        ‖toE (m + 1) y‖ ≤ (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α → y ∉ latZ p (m + 1) g) →
      LightContact (chainWR hn hraw htail) (shellR α (m + 1)) (θ α (m + 1)) g →
      Assembly.ChainOutput α g c₀

/-- **The data the drift side is invoked at.**  `LatticeDataR.rawData_exists'R`'s witnesses, with
the tail-side hypothesis still to be supplied; this is the R-lane counterpart of the `obtain` line
in `Theorem4.chainDelivers'_of_driftSide'''`, and is what makes `DriftSide''''` non-vacuous. -/
theorem exists_driftSide_dataR (m : ℕ) (hm : Threshold2.n₁ ≤ m) :
    ∃ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p) (α : ℝ), 0 < α ∧ 3 ≤ m + 1 ∧
      RawDataR p (m + 1) α ((1 - 1 / ((m + 1 : ℕ) : ℝ)) / α)
          (qC α) (shellR α (m + 1)) (A0C (m + 1)) ∧
      NormData (m + 1) α (qC α) (shellR α (m + 1)) (A0C (m + 1)) ∧
      (∀ y : Fin (m + 1) → ℤ, y ≠ 0 →
        (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α < ‖toE (m + 1) y‖ →
        ‖toE (m + 1) y‖ + Real.sqrt ((m + 1 : ℕ) : ℝ) / 2 ≤ windowR α (m + 1) →
          y ∈ shellR α (m + 1)) :=
  rawData_exists'R m hm

end Submission.L10.Theorem4R

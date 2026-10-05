import Submission.L10.DriftStopped8R
import Submission.L10.Theorem4R2

/-!
# Gate L-10 — the state supply at the reach window, keyed to the binder-free drift side

Brief 79 part 2.  The brief names this module `DriftStopped8R.lean`; that name was taken by
report 73b and is frozen (rule 5), so this is `DriftStopped8R2.lean` and it **imports** it rather
than repeating it.  Already proved there and reused unchanged: `windowOfR`, `mem_windowOfR`,
`filter_eq_windowOfR` (rule 16), `BandHypR`, `bandSideAdoptedR` and `avoid_of_casesR`.

`bandSideAdoptedR` is a **theorem** — the band is closed for good.  It carries `0 < α`, which the
assigned statement omitted; the omission makes it false (report 73b §1: at `α ≤ 0` the far-band
hypothesis is vacuously satisfied while the conclusion has a non-positive right-hand side), and
every consumer supplies it.

What is new here is the state supply keyed to `Theorem4R2.chainWR2`, i.e. with the tail-side
binder gone, and the two closing theorems.
-/

set_option linter.unusedSectionVars false

namespace Submission.L10.DriftStopped8R2

open MeasureTheory Matrix Finset Module Submission.L10 Submission.L10.Increments
open Submission.L10.ConstructionA Submission.L10.Tiling Submission.L10.PaddedLawSetup
open Submission.L10.TailSideSetup2 Submission.L10.RawDataInst2 Submission.L10.Theorem2
open Submission.L10.DriftStopped7 Submission.L10.DriftStopped8
open Submission.L10.PaddedLawSetupR Submission.L10.RawDataInst2R
open Submission.L10.LatticeDataR Submission.L10.WindowR
open Submission.L10.DriftStopped8R Submission.L10.Theorem4R2
open scoped ENNReal RealInnerProductSpace

/-- **`DriftStopped8.StateSupplyAdopted` at the reach window**, with `mLow` fixed at the adopted
lower bound and the band removed — `bandSideAdoptedR` supplies it.  This is the statement brief 76
must prove. -/
def StateSupplyAdoptedR (θ : ℝ → ℕ → ℝ≥0∞) (C' : ℝ) : Prop :=
  ∀ m : ℕ, Threshold2.n₁ ≤ m → ∀ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p) (α : ℝ),
    0 < α → ∀ (hn : 3 ≤ m + 1)
      (hraw : RawDataR p (m + 1) α ((1 - 1 / ((m + 1 : ℕ) : ℝ)) / α)
        (qC α) (shellR α (m + 1)) (A0C (m + 1)))
      (hnd : NormData (m + 1) α (qC α) (shellR α (m + 1)) (A0C (m + 1))),
      (∀ y : Fin (m + 1) → ℤ, y ≠ 0 →
        (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α < ‖toE (m + 1) y‖ →
        ‖toE (m + 1) y‖ + Real.sqrt ((m + 1 : ℕ) : ℝ) / 2 ≤ windowR α (m + 1) →
          y ∈ shellR α (m + 1)) →
      ∀ (g : Fin (m + 1) → ZMod p), g ≠ 0 →
      (∀ y : Fin (m + 1) → ℤ, y ≠ 0 →
        ‖toE (m + 1) y‖ ≤ (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α → y ∉ latZ p (m + 1) g) →
      LightContact (chainWR2 hn hraw hnd) (shellR α (m + 1)) (θ α (m + 1)) g →
      ∃ (A : EuclideanSpace ℝ (UT (m + 1))) (M : ℝ),
        A ∈ Chain.kSet (qC α) (windowOfR α p m g) ∧
        Discharge.StateBounds (symMat A) (DriftStopped6.mAdopted (m + 1)) M ∧
        ChainWiring.logDet A ≤ C' - 4 * Real.log ((m + 1 : ℕ) : ℝ)

/-- **Goal (5) at the reach window, band discharged.**  `c₀ = exp(−C'/2)`, produced.  This is
`DriftStopped8.driftSide'''_of_obligation_of_band` re-run at the R data, with `bandSideAdoptedR`
in place of the band hypothesis. -/
theorem driftSide''''_of_stateSupplyR {θ : ℝ → ℕ → ℝ≥0∞} {C' : ℝ}
    (h : StateSupplyAdoptedR θ C') :
    ∃ c₀ : ℝ, 0 < c₀ ∧ Theorem4R2.DriftSide'''' θ c₀ := by
  refine ⟨Real.exp (-C' / 2), Real.exp_pos _, ?_⟩
  intro m hm p hp hp0 α hα hn hraw hnd hcov g hg hfree hlight
  obtain ⟨A, M, hkSet, hSB, hlog⟩ := h m hm p hp hp0 α hα hn hraw hnd hcov g hg hfree hlight
  have hm0 : m ≠ 0 := by
    have h2 : 2073600 ≤ m := by simpa [Threshold2.n₁] using hm
    omega
  exact chainOutput_of_state hm0 hSB hlog
    (avoid_of_casesR hα hSB hkSet hcov hfree (bandSideAdoptedR m hm p α hα g))

/-- **The challenge statement from the state supply at the reach window**, modulo brief 71's one
link (`Theorem4R2.ParamsBridgeR`). -/
theorem klartag_packing_of_stateSupplyR {θ : ℝ → ℕ → ℝ≥0∞} {C' : ℝ}
    (hbr : Theorem4R2.ParamsBridgeR θ) (h : StateSupplyAdoptedR θ C') :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      let V := EuclideanSpace ℝ (Fin (n + 1))
      ∃ φ : V →ₗ[ℝ] V, let E := φ '' Metric.ball (0 : V) 1
        (MeasureTheory.volume E : EReal) = c * n ^ 2 ∧
        {v ∈ E | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} := by
  obtain ⟨c₀, hc₀, hd⟩ := driftSide''''_of_stateSupplyR h
  exact Theorem4R2.klartag_packing_of_driftSide'''' hc₀ hbr hd

end Submission.L10.DriftStopped8R2

import Submission.L10.DriftStopped8R5
import Submission.L10.TailAtStepR3W2
import Submission.L10.TailSideSetup3W2
import Submission.L10.Theorem2R2

/-!
# Gate L-10 — the bridge to the challenge statement at the generic reach window

Brief 85c.  Report 85b §5 item 2: 85b's twelve `…RW2` modules give the `windowR2` lane a `Params`
producer but no closing line, because `Theorem2R2`'s `wR`, `ParamsProducerR'` and final theorem
are all at `shellR`/`windowR`.  This module is that closing line, at `windowR2`.

`Theorem2.remaining_of_lemma43'` is window-free (report 79b, checked), so `klartag_packing_of_chain'R2`
re-instantiates it rather than copying it — the same eleven lines as report 79b and report 83.
-/

set_option linter.unusedSectionVars false

open MeasureTheory Finset

namespace Submission.L10.Theorem2R3

open scoped ENNReal RealInnerProductSpace
open Submission.L10 Submission.L10.Increments Submission.L10.Tiling
open Submission.L10.Assembly Submission.L10.ChainDataInst
open Submission.L10.ConstructionA Submission.L10.RawDataInst2
open Submission.L10.WindowR2 Submission.L10.ChainSetup
open Submission.L10.DriftStopped8R5

/-! ## 1. The canonical weight family at `windowR2` -/

/-- **The chain's contact weight at the generic reach window**, as a function of `(p, m, α)`;
`p` is a phantom index, exactly as in `Theorem2R2.wR`. -/
noncomputable def wR2 (_p m : ℕ) (α : ℝ) : (Fin (m + 1) → ℤ) → ℝ≥0∞ :=
  fun y => ENNReal.ofReal (ContactIntegrated.intWeight
    (gaussPath (EuclideanSpace ℝ (UT (m + 1))))
    (contactSet (qC α) (RawDataInst2RW2.shellR α (m + 1)) (A0C (m + 1))
      (step (Real.sqrt (ParamsAdopted2.stepSizeAdopted2 (m + 1)))))
    (ParamsAdopted2.stepSizeAdopted2 (m + 1)) (ParamsAdopted2.numStepsAdopted2 (m + 1)) y)

/-- The chain's own weight *is* `wR2`, definitionally — the report-83 check, re-run at `windowR2`. -/
theorem chainW_eq_wR2 {p m : ℕ} {α : ℝ} (hn : 3 ≤ m + 1)
    (hraw : PaddedLawSetupRW2.RawDataR p (m + 1) α ((1 - 1 / ((m + 1 : ℕ) : ℝ)) / α)
      (qC α) (RawDataInst2RW2.shellR α (m + 1)) (A0C (m + 1)))
    (hnd : TailSideSetup2.NormData (m + 1) α (qC α)
      (RawDataInst2RW2.shellR α (m + 1)) (A0C (m + 1))) :
    (PaddedLawSetupRW2.chainRaw2_on_setupR hn hraw
      (TailSideSetup3W2.tailSideHyp_of_rawDataR hraw hnd hn)).w = wR2 p m α := rfl

/-! ## 2. Producer, delivery, challenge statement -/

/-- **The `Params` producer at `windowR2`**, in the shape `TailAtStepR3W2` supplies. -/
def ParamsProducerR2 (θ : ℕ → ℕ → ℝ → ℝ≥0∞) : Prop :=
  ∀ (p m : ℕ) (_ : Fact (Nat.Prime p)), 2073600 ≤ m + 1 → ∀ Q : ChainRaw2RW2 p (m + 1),
    ∃ P : Params p (m + 1), P.alpha = Q.alpha ∧ P.R = Q.R ∧ P.supp = Q.supp ∧
      P.w = Q.w ∧ P.theta = θ p m Q.alpha

/-- `TailAtStepR3W2.paramsProducerR2'_of_radial` is exactly `ParamsProducerR2` at the tight
threshold family; the two hypotheses are Lemma 4.3 at the reach-2 endpoint (85b §5 item 1). -/
theorem paramsProducerR2_of_radial {C : ℕ → ℝ → ℝ}
    (hC : ∀ (m : ℕ) (α : ℝ), 2073600 ≤ m + 1 → 0 < α → 0 < C m α)
    (hrad : ∀ (m : ℕ) (α : ℝ), 2073600 ≤ m + 1 → 0 < α →
      ∫ y in Set.Ioi (0 : ℝ), y ^ (m + 1 - 1) * TailAtStepR2W2.fR4 α (m + 1) y ≤ C m α) :
    ParamsProducerR2 (fun p m α => ENNReal.ofReal (ThetaTight.thetaTight p (m + 1) (C m α))) :=
  TailAtStepR3W2.paramsProducerR2'_of_radial hC hrad

/-- **`ChainDelivers'` at the generic reach window.** -/
def ChainDelivers'R2 (θ : ℕ → ℕ → ℝ → ℝ≥0∞) (c₀ : ℝ) : Prop :=
  ∀ m : ℕ, Threshold2.n₁ ≤ m →
    ∃ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p) (Q : ChainRaw2RW2 p (m + 1)),
      ∀ g : Fin (m + 1) → ZMod p, g ≠ 0 →
        (∀ y : Fin (m + 1) → ℤ, y ≠ 0 → ‖toE (m + 1) y‖ ≤ Q.R → y ∉ latZ p (m + 1) g) →
        Theorem2.LightContact Q.w Q.supp (θ p m Q.alpha) g →
        Assembly.ChainOutput Q.alpha g c₀

/-- **Delivery from the drift side**, at the canonical weight family; the transfer is `rfl`. -/
theorem chainDelivers'R2_of_driftSideW2 {θ : ℕ → ℕ → ℝ → ℝ≥0∞} {c₀ : ℝ}
    (hd : DriftSideW2 wR2 θ c₀) : ChainDelivers'R2 θ c₀ := by
  intro m hm
  obtain ⟨p, hp, hp0, α, hα, hn, hraw, hnd, hcov⟩ := LatticeDataRW2.rawData_exists'R m hm
  refine ⟨p, hp, hp0,
    PaddedLawSetupRW2.chainRaw2_on_setupR hn hraw
      (TailSideSetup3W2.tailSideHyp_of_rawDataR hraw hnd hn),
    fun g hg hfree hlight => ?_⟩
  exact hd m hm p hp hp0 α hα hn hraw hnd hcov g hg hfree hlight

/-- **The challenge statement at `windowR2`.** -/
theorem klartag_packing_of_chain'R2 {θ : ℕ → ℕ → ℝ → ℝ≥0∞} {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hpr : ParamsProducerR2 θ) (H : ChainDelivers'R2 θ c₀) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      let V := EuclideanSpace ℝ (Fin (n + 1))
      ∃ φ : V →ₗ[ℝ] V, let E := φ '' Metric.ball (0 : V) 1
        (MeasureTheory.volume E : EReal) = c * n ^ 2 ∧
        {v ∈ E | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} := by
  refine Theorem2.remaining_of_lemma43' hc₀ (fun m hm => ?_)
  have hm' : 2073600 ≤ m + 1 := by
    have : 2073600 ≤ m := by simpa [Threshold2.n₁] using hm
    omega
  obtain ⟨p, hp, hp0, Q, h⟩ := H m hm
  obtain ⟨P, hα, hR, hsupp, hw, hθ⟩ := hpr p m hp hm' Q
  refine ⟨p, hp, hp0, P, fun g hg hfree hlight => ?_⟩
  rw [hα]
  refine h g hg (fun y hy0 hle => hfree y hy0 (by rwa [hR])) ?_
  rwa [hw, hsupp, hθ] at hlight

/-- **The challenge statement from the state supply at `windowR2` and the repaired threshold.** -/
theorem klartag_packing_of_stateSupplyR2 {c₃ : ℕ → ℝ} (hc₃0 : ∀ n, 0 ≤ c₃ n)
    (hc₃ : ∀ n, c₃ n * DriftStopped6.etaAdopted n ≤ 1 / 4)
    {θ : ℕ → ℕ → ℝ → ℝ≥0∞} {C' : ℝ}
    (hpr : ParamsProducerR2 θ) (h : StateSupplyAdoptedR2 c₃ wR2 θ C') :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      let V := EuclideanSpace ℝ (Fin (n + 1))
      ∃ φ : V →ₗ[ℝ] V, let E := φ '' Metric.ball (0 : V) 1
        (MeasureTheory.volume E : EReal) = c * n ^ 2 ∧
        {v ∈ E | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} := by
  obtain ⟨c₀, hc₀, hd⟩ := driftSideW2_of_stateSupplyR2 hc₃0 hc₃ h
  exact klartag_packing_of_chain'R2 hc₀ hpr (chainDelivers'R2_of_driftSideW2 hd)

end Submission.L10.Theorem2R3

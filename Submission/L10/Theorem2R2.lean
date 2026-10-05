import Submission.L10.Theorem2R
import Submission.L10.DriftStopped8R3
import Submission.L10.TailAtStepR2
import Submission.L10.ThetaTight

/-!
# Gate L-10 — the reach-lane bridge with the families indexed by `p`, and the tight threshold

Brief 83.  `Theorem2R.ParamsProducerR`'s `θ : ℕ → ℝ → ℝ≥0∞` cannot receive
`ThetaTight.thetaTight p n C` (report 81 §5); here `θ : ℕ → ℕ → ℝ → ℝ≥0∞`.

## Two findings about the weight family, both checked in Lean

1. **The canonical `(p, m, α)`-indexed `intWeight` family is the chain's own weight, by `rfl`**
   (`chainW_eq_wR`).  `wR` does not read `p` at all — `p` survives only as a phantom index — so
   the weight does **not** need to take `Q`, and `DriftSideW'` can be instantiated at `wR`.
2. **`ParamsProducerR'` must say `P.w = Q.w`, not `P.w = w p m Q.alpha`.**  The brief's shape is
   *not satisfiable*: `TailAtStepR2.params_of_raw2R_of_radial` sets `w := Q.w` (`:143`), and the
   predicate quantifies over **all** `Q : ChainRaw2R p (m+1)`, whose weights are arbitrary — that
   is exactly the defect report 81 §5 diagnosed, and asking `P.w = w p m Q.alpha` reproduces it on
   the other side.  With `P.w = Q.w` the fold's fifth field is `rfl` and the instantiation at `wR`
   happens once, in `chainDelivers'R'_of_driftSideW'`, where the `Q` is the chain's own.
-/

set_option linter.unusedSectionVars false

open MeasureTheory Finset

namespace Submission.L10.Theorem2R2

open scoped ENNReal RealInnerProductSpace
open Submission.L10 Submission.L10.Increments Submission.L10.Tiling
open Submission.L10.Assembly Submission.L10.ChainDataInst
open Submission.L10.ConstructionA Submission.L10.PaddedLawSetup
open Submission.L10.TailSideSetup2 Submission.L10.RawDataInst2 Submission.L10.Theorem2
open Submission.L10.PaddedLawSetupR Submission.L10.RawDataInst2R
open Submission.L10.LatticeDataR Submission.L10.TailSideSetup3
open Submission.L10.WindowR Submission.L10.DriftStopped8R Submission.L10.DriftStopped8R3
open Submission.L10.ChainSetup Submission.L10.TailAtStepR2

/-! ## 1. The canonical weight family -/

/-- **The chain's contact weight at the reach window**, as a function of `(p, m, α)`.  `p` is a
phantom index: the right-hand side does not mention it. -/
noncomputable def wR (_p m : ℕ) (α : ℝ) : (Fin (m + 1) → ℤ) → ℝ≥0∞ :=
  fun y => ENNReal.ofReal (ContactIntegrated.intWeight
    (gaussPath (EuclideanSpace ℝ (UT (m + 1))))
    (contactSet (qC α) (shellR α (m + 1)) (A0C (m + 1))
      (step (Real.sqrt (ParamsAdopted2.stepSizeAdopted2 (m + 1)))))
    (ParamsAdopted2.stepSizeAdopted2 (m + 1)) (ParamsAdopted2.numStepsAdopted2 (m + 1)) y)

/-- **Finding 1, checked**: the chain's own weight *is* `wR`, definitionally. -/
theorem chainW_eq_wR {p m : ℕ} {α : ℝ} (hn : 3 ≤ m + 1)
    (hraw : RawDataR p (m + 1) α ((1 - 1 / ((m + 1 : ℕ) : ℝ)) / α)
      (qC α) (shellR α (m + 1)) (A0C (m + 1)))
    (hnd : NormData (m + 1) α (qC α) (shellR α (m + 1)) (A0C (m + 1))) :
    (chainRaw2_on_setupR hn hraw (tailSideHyp_of_rawDataR hraw hnd hn)).w = wR p m α := rfl

/-! ## 2. The producer, the delivery, and the challenge statement -/

/-- **The `Params` producer, `p`-indexed.**  `P.w = Q.w` — see finding 2. -/
def ParamsProducerR' (θ : ℕ → ℕ → ℝ → ℝ≥0∞) : Prop :=
  ∀ (p m : ℕ) (_ : Fact (Nat.Prime p)), 2073600 ≤ m + 1 → ∀ Q : ChainRaw2R p (m + 1),
    ∃ P : Params p (m + 1), P.alpha = Q.alpha ∧ P.R = Q.R ∧ P.supp = Q.supp ∧
      P.w = Q.w ∧ P.theta = θ p m Q.alpha

/-- **`ChainDelivers'` at the reach window, `p`-indexed.** -/
def ChainDelivers'R' (θ : ℕ → ℕ → ℝ → ℝ≥0∞) (c₀ : ℝ) : Prop :=
  ∀ m : ℕ, Threshold2.n₁ ≤ m →
    ∃ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p) (Q : ChainRaw2R p (m + 1)),
      ∀ g : Fin (m + 1) → ZMod p, g ≠ 0 →
        (∀ y : Fin (m + 1) → ℤ, y ≠ 0 → ‖toE (m + 1) y‖ ≤ Q.R → y ∉ latZ p (m + 1) g) →
        LightContact Q.w Q.supp (θ p m Q.alpha) g →
        Assembly.ChainOutput Q.alpha g c₀

/-- **Delivery from the drift side**, instantiated at the canonical weight family; the transfer
`Q.w = wR p m α` is `chainW_eq_wR`, i.e. `rfl`. -/
theorem chainDelivers'R'_of_driftSideW' {θ : ℕ → ℕ → ℝ → ℝ≥0∞} {c₀ : ℝ}
    (hd : DriftSideW' wR θ c₀) : ChainDelivers'R' θ c₀ := by
  intro m hm
  obtain ⟨p, hp, hp0, α, hα, hn, hraw, hnd, hcov⟩ := rawData_exists'R m hm
  refine ⟨p, hp, hp0,
    chainRaw2_on_setupR hn hraw (tailSideHyp_of_rawDataR hraw hnd hn),
    fun g hg hfree hlight => ?_⟩
  exact hd m hm p hp hp0 α hα hn hraw hnd hcov g hg hfree hlight

/-- **The challenge statement**, re-instantiating `Theorem2.remaining_of_lemma43'` (window-free). -/
theorem klartag_packing_of_chain'R' {θ : ℕ → ℕ → ℝ → ℝ≥0∞} {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hpr : ParamsProducerR' θ) (H : ChainDelivers'R' θ c₀) :
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

/-- **The challenge statement from the state supply**, `p`-indexed. -/
theorem klartag_packing_of_stateSupplyR' {θ : ℕ → ℕ → ℝ → ℝ≥0∞} {C' : ℝ}
    (hpr : ParamsProducerR' θ) (h : StateSupplyAdoptedR' wR θ C') :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      let V := EuclideanSpace ℝ (Fin (n + 1))
      ∃ φ : V →ₗ[ℝ] V, let E := φ '' Metric.ball (0 : V) 1
        (MeasureTheory.volume E : EReal) = c * n ^ 2 ∧
        {v ∈ E | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} := by
  obtain ⟨c₀, hc₀, hd⟩ := driftSide'''''_of_stateSupplyR' h
  exact klartag_packing_of_chain'R' hc₀ hpr (chainDelivers'R'_of_driftSideW' hd)

/-! ## 3. The fold-in, and the tight threshold -/

/-- **Brief 71's two outputs**, in the shape `TailAtStepR2.params_of_raw2R_of_radial` consumes. -/
def Brief71 (C : ℕ → ℝ → ℝ) : Prop :=
  (∀ (n : ℕ) (α : ℝ), 0 < C n α) ∧
  ∀ (n : ℕ) (α : ℝ), ∫ y in Set.Ioi (0 : ℝ), y ^ (n - 1) * fR4 α n y ≤ C n α

/-- **`ParamsProducerR'` from brief 81's fold-in.**  All five fields are `rfl`
(`TailAtStepR2.params_fields`); the only inputs are brief 71's constant and radial bound. -/
theorem paramsProducerR'_of_fold {C : ℕ → ℝ → ℝ} (h71 : Brief71 C) :
    ParamsProducerR' (fun p m α => ENNReal.ofReal (ThetaTight.thetaTight p (m + 1) (C (m + 1) α))) := by
  intro p m hp hm Q
  exact ⟨params_of_raw2R_of_radial hm Q (h71.1 (m + 1) Q.alpha) (h71.2 (m + 1) Q.alpha),
    params_fields hm Q (h71.1 (m + 1) Q.alpha) (h71.2 (m + 1) Q.alpha)⟩

/-- **The specialised final line**: at the canonical weight family and the tight threshold, the
state supply closes the challenge statement outright, given brief 71. -/
theorem klartag_packing_of_stateSupplyR'_tight {C : ℕ → ℝ → ℝ} (h71 : Brief71 C) {C' : ℝ}
    (h : StateSupplyAdoptedR' wR
      (fun p m α => ENNReal.ofReal (ThetaTight.thetaTight p (m + 1) (C (m + 1) α))) C') :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      let V := EuclideanSpace ℝ (Fin (n + 1))
      ∃ φ : V →ₗ[ℝ] V, let E := φ '' Metric.ball (0 : V) 1
        (MeasureTheory.volume E : EReal) = c * n ^ 2 ∧
        {v ∈ E | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} :=
  klartag_packing_of_stateSupplyR' (paramsProducerR'_of_fold h71) h

end Submission.L10.Theorem2R2

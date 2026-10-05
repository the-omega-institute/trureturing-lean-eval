import Submission.L10.DriftStopped8R
import Submission.L10.TailSideSetup3
import Submission.L10.LatticeDataR

/-!
# Gate L-10 — `Theorem2` at the reach window: the bridge to the challenge statement

Brief 79 (re-scoped).  Nothing at the reach window reached the challenge statement; this module is
that bridge, keyed to report 73b's `DriftStopped8R.DriftSideW` and `StateSupplyAdoptedR`.

**Two of `Theorem2`'s three links are reused, not copied** — checked, not assumed:
`Assembly.exists_phi_of_params'` and `Theorem2.remaining_of_lemma43'` are stated over
`ChainDataInst.Params` and read only `P.alpha`, `P.R`, `P.w`, `P.supp`, `P.theta`.  Nothing in
either mentions a window, so the reach lane instantiates them unchanged.

**The third link is parametric.**  `Theorem2.lemma43_input_of_raw2'` goes through
`TailAtStep.params_of_raw2`, whose reach analogue `params_of_raw2R` is brief 72's held fold-in
(waiting on brief 71's Lemma 4.3 at `windowR` and brief 77's threshold).  It enters here as
`ParamsProducerR`, carrying exactly the five field equalities `remaining_of_lemma43'` reads.
`paramsProducerR_of_fold` is the one-line stub to fill when the fold-in lands.
-/

set_option linter.unusedSectionVars false

open MeasureTheory Finset

namespace Submission.L10.Theorem2R

open scoped ENNReal RealInnerProductSpace
open Submission.L10 Submission.L10.Increments Submission.L10.Tiling
open Submission.L10.Assembly Submission.L10.ChainDataInst
open Submission.L10.ConstructionA Submission.L10.PaddedLawSetup
open Submission.L10.TailSideSetup2 Submission.L10.RawDataInst2 Submission.L10.Theorem2
open Submission.L10.PaddedLawSetupR Submission.L10.RawDataInst2R
open Submission.L10.LatticeDataR Submission.L10.TailSideSetup3
open Submission.L10.WindowR Submission.L10.DriftStopped8R

/-! ## 1. The one held link, as a parameter -/

/-- **The `Params` producer at the reach window** — brief 72's held `params_of_raw2R`, reduced to
the five facts `Theorem2.remaining_of_lemma43'` actually reads. -/
def ParamsProducerR (w : ∀ m : ℕ, ℝ → (Fin (m + 1) → ℤ) → ℝ≥0∞) (θ : ℕ → ℝ → ℝ≥0∞) : Prop :=
  ∀ (p m : ℕ) (_ : Fact (Nat.Prime p)), 2073600 ≤ m + 1 → ∀ Q : ChainRaw2R p (m + 1),
    ∃ P : Params p (m + 1), P.alpha = Q.alpha ∧ P.R = Q.R ∧ P.supp = Q.supp ∧
      P.w = w m Q.alpha ∧ P.theta = θ m Q.alpha

/-! ## 2. `ChainDelivers'` at the reach window, data first -/

/-- **`Theorem2.ChainDelivers'` at the reach window**, with the light-contact clause carrying the
parametric weight and threshold of report 73b / report 74 §4. -/
def ChainDelivers'R (w : ∀ m : ℕ, ℝ → (Fin (m + 1) → ℤ) → ℝ≥0∞) (θ : ℕ → ℝ → ℝ≥0∞)
    (c₀ : ℝ) : Prop :=
  ∀ m : ℕ, Threshold2.n₁ ≤ m →
    ∃ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p) (Q : ChainRaw2R p (m + 1)),
      ∀ g : Fin (m + 1) → ZMod p, g ≠ 0 →
        (∀ y : Fin (m + 1) → ℤ, y ≠ 0 → ‖toE (m + 1) y‖ ≤ Q.R → y ∉ latZ p (m + 1) g) →
        LightContact (w m Q.alpha) Q.supp (θ m Q.alpha) g →
        Assembly.ChainOutput Q.alpha g c₀

/-- **`ChainDelivers'R` from the drift side.**  The witnesses are `LatticeDataR.rawData_exists'R`'s
and the chain is `chainRaw2_on_setupR` with brief 78's producer, so `Q.alpha = α`, `Q.R = R` and
`Q.supp = shellR α (m+1)` all hold by `rfl` — the same three identifications the `windowC` lane
rests on. -/
theorem chainDelivers'R_of_driftSideW
    {w : ∀ m : ℕ, ℝ → (Fin (m + 1) → ℤ) → ℝ≥0∞} {θ : ℕ → ℝ → ℝ≥0∞} {c₀ : ℝ}
    (hd : DriftSideW w θ c₀) : ChainDelivers'R w θ c₀ := by
  intro m hm
  obtain ⟨p, hp, hp0, α, hα, hn, hraw, hnd, hcov⟩ := rawData_exists'R m hm
  refine ⟨p, hp, hp0,
    chainRaw2_on_setupR hn hraw (tailSideHyp_of_rawDataR hraw hnd hn),
    fun g hg hfree hlight => ?_⟩
  exact hd m hm p hp hp0 α hα hn hraw hnd hcov g hg hfree hlight

/-! ## 3. The challenge statement -/

/-- **`Theorem2.klartag_packing_of_chain'` at the reach window**, a re-instantiation of
`remaining_of_lemma43'` (general in the window) rather than a copy. -/
theorem klartag_packing_of_chain'R
    {w : ∀ m : ℕ, ℝ → (Fin (m + 1) → ℤ) → ℝ≥0∞} {θ : ℕ → ℝ → ℝ≥0∞} {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hpr : ParamsProducerR w θ) (H : ChainDelivers'R w θ c₀) :
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

/-- **The challenge statement from the drift side at the reach window.** -/
theorem klartag_packing_of_driftSideW
    {w : ∀ m : ℕ, ℝ → (Fin (m + 1) → ℤ) → ℝ≥0∞} {θ : ℕ → ℝ → ℝ≥0∞} {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hpr : ParamsProducerR w θ) (hd : DriftSideW w θ c₀) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      let V := EuclideanSpace ℝ (Fin (n + 1))
      ∃ φ : V →ₗ[ℝ] V, let E := φ '' Metric.ball (0 : V) 1
        (MeasureTheory.volume E : EReal) = c * n ^ 2 ∧
        {v ∈ E | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} :=
  klartag_packing_of_chain'R hc₀ hpr (chainDelivers'R_of_driftSideW hd)

/-- **The challenge statement from the state supply**, composing report 73b's
`driftSide''''_of_stateSupplyR` — `c₀ = exp(−C'/2)` is produced, not assumed. -/
theorem klartag_packing_of_stateSupplyR
    {w : ∀ m : ℕ, ℝ → (Fin (m + 1) → ℤ) → ℝ≥0∞} {θ : ℕ → ℝ → ℝ≥0∞} {C' : ℝ}
    (hpr : ParamsProducerR w θ) (h : StateSupplyAdoptedR w θ C') :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      let V := EuclideanSpace ℝ (Fin (n + 1))
      ∃ φ : V →ₗ[ℝ] V, let E := φ '' Metric.ball (0 : V) 1
        (MeasureTheory.volume E : EReal) = c * n ^ 2 ∧
        {v ∈ E | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} := by
  obtain ⟨c₀, hc₀, hd⟩ := driftSide''''_of_stateSupplyR h
  exact klartag_packing_of_driftSideW hc₀ hpr hd

/-! ## 4. The specialisation stub -/

/-- **The one line to fill when brief 72's fold-in lands.**  `params_of_raw2R` is to return a
`Params p n` whose `alpha`, `R`, `supp` are `Q`'s and whose `w`, `theta` are the adopted weight and
threshold — in the `windowC` lane `TailAtStep.params_of_raw2` gives all five by `rfl`.  Given it in
that shape, `ParamsProducerR` follows immediately. -/
theorem paramsProducerR_of_fold {w : ∀ m : ℕ, ℝ → (Fin (m + 1) → ℤ) → ℝ≥0∞}
    {θ : ℕ → ℝ → ℝ≥0∞}
    (fold : ∀ (p m : ℕ) (_ : Fact (Nat.Prime p)), 2073600 ≤ m + 1 →
      ∀ Q : ChainRaw2R p (m + 1), ∃ P : Params p (m + 1),
        P.alpha = Q.alpha ∧ P.R = Q.R ∧ P.supp = Q.supp ∧
        P.w = w m Q.alpha ∧ P.theta = θ m Q.alpha) :
    ParamsProducerR w θ := fold

end Submission.L10.Theorem2R

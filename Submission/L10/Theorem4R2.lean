import Submission.L10.Theorem4R
import Submission.L10.TailSideSetup3
import Submission.L10.LatticeDataR

/-!
# Gate L-10 — the drift-side predicate at the reach window, with the binders dropped

Brief 79 part 1.  Brief 78's `TailSideSetup3.tailSideHyp_of_rawDataR` closes the gap report 73
named, so the reach lane's weight is computable from `hraw` and `hnd` alone.  `DriftSide''''`
below is therefore **textually** `Theorem4.DriftSide'''` under `windowC → windowR`,
`shell → shellR`, `ENNReal.ofReal (64 · C1C α (m+1)) → θ α (m+1)` — no extra binder, and the
scale is pinned rather than quantified.  `Theorem4R.DriftSide''''` (report 73) carried an `htail`
binder for exactly the missing producer; it is superseded here and `Theorem4R.lean`, being
reported, is untouched.

## The R-assembly is a re-instantiation, and one link is missing

`Theorem2.remaining_of_lemma43'` reads only `P.alpha`, `P.R`, `P.w`, `P.supp`, `P.theta` and is
**general in the window**, so the reach lane needs no copy of it.  The single missing link is
brief 71's `params_of_raw2R : ChainRaw2R p n → ChainDataInst.Params p n`, the analogue of
`TailAtStep.params_of_raw2`; `TailAtStepR` (brief 72) deferred it.  It is isolated here as
`ParamsBridgeR`, whose five components `params_of_raw2` proves by `rfl` in the `windowC` lane, so
brief 71's deliverable discharges it in one line.
-/

set_option linter.unusedSectionVars false

open MeasureTheory Finset

namespace Submission.L10.Theorem4R2

open scoped ENNReal RealInnerProductSpace
open Submission.L10 Submission.L10.Increments Submission.L10.Tiling
open Submission.L10.Assembly Submission.L10.ChainDataInst
open Submission.L10.ConstructionA Submission.L10.PaddedLawSetup
open Submission.L10.TailSideSetup2 Submission.L10.RawDataInst2 Submission.L10.Theorem2
open Submission.L10.PaddedLawSetupR Submission.L10.RawDataInst2R
open Submission.L10.LatticeDataR Submission.L10.TailSideSetup3 Submission.L10.WindowR

/-! ## 1. The weight, with no binder -/

/-- **The chain's weight at the reach window.**  `Theorem2.chainW` with `chainRaw2_on_setupR` and
brief 78's producer; no tail-side binder. -/
noncomputable def chainWR2 {p m : ℕ} {α R : ℝ}
    {q : (Fin (m + 1) → ℤ) → EuclideanSpace ℝ (UT (m + 1))} {W : Finset (Fin (m + 1) → ℤ)}
    {A₀ : EuclideanSpace ℝ (UT (m + 1))} (hn : 3 ≤ m + 1)
    (hraw : RawDataR p (m + 1) α R q W A₀) (hnd : NormData (m + 1) α q W A₀) :
    (Fin (m + 1) → ℤ) → ℝ≥0∞ :=
  (chainRaw2_on_setupR hn hraw (tailSideHyp_of_rawDataR hraw hnd hn)).w

/-! ## 2. The drift side -/

/-- **`Theorem4.DriftSide'''` at the reach window.**  Binder for binder the same; `θ` replaces the
closed form `ENNReal.ofReal (64 · C1C α (m+1))` until briefs 71/77 pin it. -/
def DriftSide'''' (θ : ℝ → ℕ → ℝ≥0∞) (c₀ : ℝ) : Prop :=
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
      Assembly.ChainOutput α g c₀

/-! ## 3. `ChainDelivers'` at the reach window -/

/-- **`Theorem2.ChainDelivers'` at the reach window.** -/
def ChainDelivers'R (θ : ℝ → ℕ → ℝ≥0∞) (c₀ : ℝ) : Prop :=
  ∀ m : ℕ, Threshold2.n₁ ≤ m →
    ∃ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p) (Q : ChainRaw2R p (m + 1)),
      ∀ g : Fin (m + 1) → ZMod p, g ≠ 0 →
        (∀ y : Fin (m + 1) → ℤ, y ≠ 0 → ‖toE (m + 1) y‖ ≤ Q.R → y ∉ latZ p (m + 1) g) →
        LightContact Q.w Q.supp (θ Q.alpha (m + 1)) g →
        Assembly.ChainOutput Q.alpha g c₀

/-- **`ChainDelivers'R` from the drift side**, at `rawData_exists'R`'s own witnesses — so the
drift side is only ever invoked at the reach shell. -/
theorem chainDelivers'R_of_driftSide'''' {θ : ℝ → ℕ → ℝ≥0∞} {c₀ : ℝ}
    (hd : DriftSide'''' θ c₀) : ChainDelivers'R θ c₀ := by
  intro m hm
  obtain ⟨p, hp, hp0, α, hα, hn, hraw, hnd, hcov⟩ := rawData_exists'R m hm
  exact ⟨p, hp, hp0,
    chainRaw2_on_setupR hn hraw (tailSideHyp_of_rawDataR hraw hnd hn),
    fun g hg hfree hlight => hd m hm p hp hp0 α hα hn hraw hnd hcov g hg hfree hlight⟩

/-! ## 4. The assembly, modulo brief 71's one link -/

/-- **The one missing link**, isolated: brief 71's `params_of_raw2R`.  `TailAtStep.params_of_raw2`
proves all five components by `rfl` in the `windowC` lane. -/
def ParamsBridgeR (θ : ℝ → ℕ → ℝ≥0∞) : Prop :=
  ∀ (p n : ℕ) (_ : Fact (Nat.Prime p)), 2073600 ≤ n → ∀ Q : ChainRaw2R p n,
    ∃ P : Params p n, P.alpha = Q.alpha ∧ P.R = Q.R ∧ P.w = Q.w ∧ P.supp = Q.supp ∧
      P.theta = θ Q.alpha n

/-- **`Theorem2.lemma43_input_of_raw2'` at the reach window**, a re-instantiation of
`remaining_of_lemma43'` (which is general in the window), not a copy. -/
theorem lemma43_input_of_raw2'R {θ : ℝ → ℕ → ℝ≥0∞} {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hbr : ParamsBridgeR θ) (H : ChainDelivers'R θ c₀) :
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
  obtain ⟨P, hα, hR, hw, hsupp, hθ⟩ := hbr p (m + 1) hp hm' Q
  refine ⟨p, hp, hp0, P, fun g hg hfree hlight => ?_⟩
  rw [hα]
  refine h g hg (fun y hy0 hle => hfree y hy0 (by rwa [hR])) ?_
  rwa [hw, hsupp, hθ] at hlight

/-- **The challenge statement from the drift side at the reach window.** -/
theorem klartag_packing_of_driftSide'''' {θ : ℝ → ℕ → ℝ≥0∞} {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hbr : ParamsBridgeR θ) (hd : DriftSide'''' θ c₀) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      let V := EuclideanSpace ℝ (Fin (n + 1))
      ∃ φ : V →ₗ[ℝ] V, let E := φ '' Metric.ball (0 : V) 1
        (MeasureTheory.volume E : EReal) = c * n ^ 2 ∧
        {v ∈ E | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} :=
  lemma43_input_of_raw2'R hc₀ hbr (chainDelivers'R_of_driftSide'''' hd)

end Submission.L10.Theorem4R2

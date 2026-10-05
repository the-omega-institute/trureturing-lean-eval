import Submission.L10.Theorem2R3
import Submission.L10.GoodPathLightR2
import Submission.L10.TailAtStepR5W2
import Submission.L10.DriftStopped6c

/-!
# Gate L-10 — the bridge over `ChainRaw3`: one combined light-contact hypothesis

Brief 91, re-cut on the lead's 85f route note.  Report 85f's `ChainRaw3` carries both weights and
`paramsProducer3` sets `P.w = combW A B Q`, so `Theorem2R3.ParamsProducerR2` — which binds
`ChainRaw2RW2` with `P.w = Q.w` — cannot receive it.  This module is the bridge re-stated over
`ChainRaw3`, the same substitution `GoodPathAt2` needed for the window.

**The weight is `g`-free and chain-free.**  `TailAtStepR5W2.chainRaw3_of_raw2` swaps any
`ChainRaw2RW2` into a `ChainRaw3` whose two weights are the `profileAt` bounds themselves
(`wProf`, `wProfT`), both tail fields `le_refl`.  So `combW A B (chainRaw3_of_raw2 Q)` depends on
`Q` only through `Q.alpha`: it *is* the `(p, m, α)`-family `wComb`, by `rfl` (`combW_eq_wComb`).
That is what makes the light-contact hypothesis of `LightGoodPath3` datum-free.

**One light-contact hypothesis, not two.**  `TailAtStepR5W2.both_sums_windowR2` takes exactly this
hypothesis at `wComb` on `shellR` and returns both sums for the `windowOfR2` chain; `combW_eq_wComb`
is the rewrite that moves `LightGoodPath3`'s hypothesis into its shape.

**The `c₃` clamp.**  `GoodPathLightR2.stateSupplyAdoptedR2_of_goodPathAt` (frozen) asks for
`∀ n, c₃ n * η n ≤ 1/4`, while `DriftStopped6c.c3Adopted''_eta_le` proves it only at
`n ≥ 2 073 600`.  `c3clamp` is `c3Adopted''` above the threshold and `0` below, which satisfies the
unrestricted form and agrees with `c3Adopted''` wherever it is used (`c3clamp_eq`), so
`LightGoodPath3` is stated at `DriftStopped6c.c3Adopted''` itself.
-/

set_option linter.unusedSectionVars false

open MeasureTheory Finset

namespace Submission.L10.Theorem2R4

open scoped ENNReal RealInnerProductSpace
open Submission.L10 Submission.L10.Increments Submission.L10.Tiling
open Submission.L10.Assembly Submission.L10.ChainDataInst
open Submission.L10.ConstructionA Submission.L10.RawDataInst2
open Submission.L10.WindowR2 Submission.L10.ChainSetup
open Submission.L10.DriftStopped8R5 Submission.L10.Theorem2R3
open Submission.L10.GoodPathLightR2 Submission.L10.TailAtStepR5W2

/-! ## 1. The combined profile weight, as a `(p, m, α)`-family -/

/-- **The combined `profileAt` weight.**  No chain, no `g`, no record: a function of `(A, B, α, m)`
alone.  This is the weight the light-contact hypothesis is stated at. -/
noncomputable def wComb (A B : ℝ) (_p m : ℕ) (α : ℝ) : (Fin (m + 1) → ℤ) → ℝ≥0∞ :=
  fun y => ENNReal.ofReal A * wProf α (m + 1) y + ENNReal.ofReal B * wProfT α (m + 1) y

/-- **The transfer, definitional.**  `chainRaw3_of_raw2` installs the profile bounds as the
weights, so `combW` at it is `wComb`.  This is the rewrite `both_sums_windowR2` needs. -/
theorem combW_eq_wComb {p m : ℕ} (A B : ℝ) (Q : ChainRaw2RW2 p (m + 1)) :
    combW A B (chainRaw3_of_raw2 Q) = wComb A B p m Q.alpha := rfl

/-- The canonical `ChainRaw3` at the adopted data: the reach-2 chain record, weights swapped. -/
noncomputable def QOf {p m : ℕ} {α : ℝ} (hn : 3 ≤ m + 1)
    (hraw : PaddedLawSetupRW2.RawDataR p (m + 1) α ((1 - 1 / ((m + 1 : ℕ) : ℝ)) / α)
      (qC α) (RawDataInst2RW2.shellR α (m + 1)) (A0C (m + 1)))
    (hnd : TailSideSetup2.NormData (m + 1) α (qC α)
      (RawDataInst2RW2.shellR α (m + 1)) (A0C (m + 1))) : ChainRaw3 p (m + 1) :=
  chainRaw3_of_raw2 (PaddedLawSetupRW2.chainRaw2_on_setupR hn hraw
    (TailSideSetup3W2.tailSideHyp_of_rawDataR hraw hnd hn))

/-- The combined threshold family, in the shape `paramsProducer3` returns. -/
noncomputable def θ3 (A B : ℝ) (p m : ℕ) (α : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (ThetaTight.thetaTight p (m + 1) (C3 (m + 1) A B α))

/-! ## 2. `ChainDelivers'` over `ChainRaw3`, and the challenge statement -/

/-- **`ChainDelivers'` over `ChainRaw3`**, with the single combined light-contact hypothesis. -/
def ChainDelivers'R3 (A B : ℝ) (c₀ : ℝ) : Prop :=
  ∀ m : ℕ, Threshold2.n₁ ≤ m →
    ∃ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p) (Q : ChainRaw3 p (m + 1)),
      ∀ g : Fin (m + 1) → ZMod p, g ≠ 0 →
        (∀ y : Fin (m + 1) → ℤ, y ≠ 0 → ‖toE (m + 1) y‖ ≤ Q.R → y ∉ latZ p (m + 1) g) →
        Theorem2.LightContact (combW A B Q) Q.supp (θ3 A B p m Q.alpha) g →
        Assembly.ChainOutput Q.alpha g c₀

/-- **The challenge statement over `ChainRaw3`** — report 79b's eleven lines with
`TailAtStepR5W2.paramsProducer3`. -/
theorem klartag_packing_of_chain'R3 {A B c₀ : ℝ} (hc₀ : 0 < c₀) (hA : 0 < A) (hB : 0 ≤ B)
    (H : ChainDelivers'R3 A B c₀) :
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
  obtain ⟨P, hα, hR, hsupp, hw, hθ⟩ := paramsProducer3 hA hB p m hp hm' Q
  refine ⟨p, hp, hp0, P, fun g hg hfree hlight => ?_⟩
  rw [hα]
  refine h g hg (fun y hy0 hle => hfree y hy0 (by rwa [hR])) ?_
  rwa [hw, hsupp, hθ] at hlight

/-! ## 3. The drift side and the state supply at the combined weight -/

/-- **The drift side over `ChainRaw3`.**  The light-contact hypothesis is at the `g`-free
`wComb` on `shellR`: no record, no chain. -/
def DriftSideW3 (A B : ℝ) (c₀ : ℝ) : Prop :=
  ∀ m : ℕ, Threshold2.n₁ ≤ m → ∀ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p) (α : ℝ),
    0 < α → ∀ (_hn : 3 ≤ m + 1)
      (_hraw : PaddedLawSetupRW2.RawDataR p (m + 1) α ((1 - 1 / ((m + 1 : ℕ) : ℝ)) / α)
        (qC α) (RawDataInst2RW2.shellR α (m + 1)) (A0C (m + 1)))
      (_hnd : TailSideSetup2.NormData (m + 1) α (qC α)
        (RawDataInst2RW2.shellR α (m + 1)) (A0C (m + 1))),
      (∀ y : Fin (m + 1) → ℤ, y ≠ 0 →
        (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α < ‖toE (m + 1) y‖ →
        ‖toE (m + 1) y‖ + Real.sqrt ((m + 1 : ℕ) : ℝ) / 2 ≤ windowR2 α (m + 1) →
          y ∈ RawDataInst2RW2.shellR α (m + 1)) →
      ∀ (g : Fin (m + 1) → ZMod p), g ≠ 0 →
      (∀ y : Fin (m + 1) → ℤ, y ≠ 0 →
        ‖toE (m + 1) y‖ ≤ (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α → y ∉ latZ p (m + 1) g) →
      Theorem2.LightContact (wComb A B p m α)
        (RawDataInst2RW2.shellR α (m + 1)) (θ3 A B p m α) g →
      Assembly.ChainOutput α g c₀

/-- **The state supply at the combined weight**, at `mAt (m+1) c₃`. -/
def StateSupplyAdoptedR3 (A B : ℝ) (c₃ : ℕ → ℝ) (C' : ℝ) : Prop :=
  ∀ m : ℕ, Threshold2.n₁ ≤ m → ∀ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p) (α : ℝ),
    0 < α → ∀ (_hn : 3 ≤ m + 1)
      (_hraw : PaddedLawSetupRW2.RawDataR p (m + 1) α ((1 - 1 / ((m + 1 : ℕ) : ℝ)) / α)
        (qC α) (RawDataInst2RW2.shellR α (m + 1)) (A0C (m + 1)))
      (_hnd : TailSideSetup2.NormData (m + 1) α (qC α)
        (RawDataInst2RW2.shellR α (m + 1)) (A0C (m + 1))),
      (∀ y : Fin (m + 1) → ℤ, y ≠ 0 →
        (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α < ‖toE (m + 1) y‖ →
        ‖toE (m + 1) y‖ + Real.sqrt ((m + 1 : ℕ) : ℝ) / 2 ≤ windowR2 α (m + 1) →
          y ∈ RawDataInst2RW2.shellR α (m + 1)) →
      ∀ (g : Fin (m + 1) → ZMod p), g ≠ 0 →
      (∀ y : Fin (m + 1) → ℤ, y ≠ 0 →
        ‖toE (m + 1) y‖ ≤ (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α → y ∉ latZ p (m + 1) g) →
      Theorem2.LightContact (wComb A B p m α)
        (RawDataInst2RW2.shellR α (m + 1)) (θ3 A B p m α) g →
      ∃ (A' : EuclideanSpace ℝ (UT (m + 1))) (M : ℝ),
        A' ∈ Chain.kSet (qC α) (windowOfR2 α p m g) ∧
        Discharge.StateBounds (symMat A') (GoodPathBounds.mAt (m + 1) (c₃ (m + 1))) M ∧
        ChainWiring.logDet A' ≤ C' - 4 * Real.log ((m + 1 : ℕ) : ℝ)

/-- **Goal (5) at the combined weight**; the band is `bandSideAdoptedR2`, generic in `c₃`. -/
theorem driftSideW3_of_stateSupplyR3 {A B : ℝ} {c₃ : ℕ → ℝ} (hc₃0 : ∀ n, 0 ≤ c₃ n)
    (hc₃ : ∀ n, c₃ n * DriftStopped6.etaAdopted n ≤ 1 / 4) {C' : ℝ}
    (h : StateSupplyAdoptedR3 A B c₃ C') :
    ∃ c₀ : ℝ, 0 < c₀ ∧ DriftSideW3 A B c₀ := by
  refine ⟨Real.exp (-C' / 2), Real.exp_pos _, ?_⟩
  intro m hm p hp hp0 α hα hn hraw hnd hcov g hg hfree hlight
  obtain ⟨A', M, hkSet, hSB, hlog⟩ := h m hm p hp hp0 α hα hn hraw hnd hcov g hg hfree hlight
  have hm0 : m ≠ 0 := by
    have h2 : 2073600 ≤ m := by simpa [Threshold2.n₁] using hm
    omega
  exact DriftStopped8.chainOutput_of_state hm0 hSB hlog
    (avoid_of_casesR2 hα hSB hkSet hcov hfree (bandSideAdoptedR2 hc₃0 hc₃ m hm p α hα g))

/-- **Delivery**: the canonical `QOf` has `alpha`, `R`, `supp` and `combW` by `rfl`. -/
theorem chainDelivers'R3_of_driftSideW3 {A B c₀ : ℝ} (hd : DriftSideW3 A B c₀) :
    ChainDelivers'R3 A B c₀ := by
  intro m hm
  obtain ⟨p, hp, hp0, α, hα, hn, hraw, hnd, hcov⟩ := LatticeDataRW2.rawData_exists'R m hm
  exact ⟨p, hp, hp0, QOf hn hraw hnd,
    fun g hg hfree hlight => hd m hm p hp hp0 α hα hn hraw hnd hcov g hg hfree hlight⟩

/-! ## 4. The light-line hand-off, and the closing line -/

/-- `c3Adopted''` clamped below the threshold, so the unrestricted admissibility facts hold. -/
noncomputable def c3clamp (n : ℕ) : ℝ :=
  if 2073600 ≤ n then DriftStopped6c.c3Adopted'' n else 0

theorem c3clamp_nonneg (n : ℕ) : 0 ≤ c3clamp n := by
  rw [c3clamp]; split
  · exact DriftStopped6c.c3Adopted''_nonneg n
  · exact le_refl 0

theorem c3clamp_eta_le (n : ℕ) :
    c3clamp n * DriftStopped6.etaAdopted n ≤ 1 / 4 := by
  rw [c3clamp]; split
  · rename_i h; exact DriftStopped6c.c3Adopted''_eta_le h
  · rw [zero_mul]; norm_num

theorem c3clamp_eq {n : ℕ} (hn : 2073600 ≤ n) : c3clamp n = DriftStopped6c.c3Adopted'' n := by
  rw [c3clamp, ite_eq_left hn]

/-- **The statement brief 90 discharges.** -/
def LightGoodPath3 (A B : ℝ) (C' : ℝ) : Prop :=
  ∀ m : ℕ, Threshold2.n₁ ≤ m → ∀ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p) (α : ℝ),
    0 < α → ∀ (_hn : 3 ≤ m + 1)
      (_hraw : PaddedLawSetupRW2.RawDataR p (m + 1) α ((1 - 1 / ((m + 1 : ℕ) : ℝ)) / α)
        (qC α) (RawDataInst2RW2.shellR α (m + 1)) (A0C (m + 1)))
      (_hnd : TailSideSetup2.NormData (m + 1) α (qC α)
        (RawDataInst2RW2.shellR α (m + 1)) (A0C (m + 1))),
      ∀ g : Fin (m + 1) → ZMod p, g ≠ 0 →
      (∀ y : Fin (m + 1) → ℤ, y ≠ 0 →
        ‖toE (m + 1) y‖ ≤ (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α → y ∉ latZ p (m + 1) g) →
      Theorem2.LightContact (wComb A B p m α)
        (RawDataInst2RW2.shellR α (m + 1)) (θ3 A B p m α) g →
      GoodPathAt2 p m α g (DriftStopped6c.c3Adopted'' (m + 1)) C'

/-- **`StateSupplyAdoptedR3` from the light-line form** — `stateTriple_of_goodPathAt2` at `mAt`. -/
theorem stateSupplyAdoptedR3_of_lightGoodPath3 {A B C' : ℝ} (h : LightGoodPath3 A B C') :
    StateSupplyAdoptedR3 A B c3clamp C' := by
  intro m hm p hp hp0 α hα hn hraw hnd _hcov g hg hfree hlight
  have hm1 : 2073600 ≤ m + 1 := by
    have h2 : 2073600 ≤ m := by simpa [Threshold2.n₁] using hm
    omega
  rw [c3clamp_eq hm1]
  exact stateTriple_of_goodPathAt2 hm (DriftStopped6c.c3Adopted''_nonneg (m + 1))
    (DriftStopped6c.c3Adopted''_eta_le hm1) hraw
    (h m hm p hp hp0 α hα hn hraw hnd g hg hfree hlight)

/-- **The gate from the combined light-line hypothesis, with no other hypothesis.** -/
theorem klartag_packing_of_lightGoodPath3 {A B : ℝ} (hA : 0 < A) (hB : 0 ≤ B) {C' : ℝ}
    (h : LightGoodPath3 A B C') :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      let V := EuclideanSpace ℝ (Fin (n + 1))
      ∃ φ : V →ₗ[ℝ] V, let E := φ '' Metric.ball (0 : V) 1
        (MeasureTheory.volume E : EReal) = c * n ^ 2 ∧
        {v ∈ E | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} := by
  obtain ⟨c₀, hc₀, hd⟩ := driftSideW3_of_stateSupplyR3 c3clamp_nonneg c3clamp_eta_le
    (stateSupplyAdoptedR3_of_lightGoodPath3 h)
  exact klartag_packing_of_chain'R3 hc₀ hA hB (chainDelivers'R3_of_driftSideW3 hd)

end Submission.L10.Theorem2R4

/-
Gate L-10 (`klartag_packing`), brief 100 Part A — the `B`-family: the nine declarations of the
closing chain re-cut with the terminal coefficient **depending on the dimension**.

`Theorem2R4.wComb (A B : ℝ)` and everything above it carry `B : ℝ` *outside* the `∀ m`, but
`TailAtStepR5W2.C3 n A B α = A·4·C1R·(8 − 8/n²) + 4·B·C1cR·n²` is linear in `B` with an `n²`
attached, so a fixed positive real `B` forces the integrated contact threshold `Θ` to carry
`(B/A)·n²` — and `Θ` enters the budget numerator as `+cqAt·Θ`, which no fixed `C'` can absorb
(report `99-final-theorem.md` §2).  Report 74 §4's design had the terminal coefficient
proportional to `1/n²`; freezing it as a real is the bug.

Every proof in the chain is already per-`m`, so the repair is syntactic: the same nine statements
with `(B : ℕ → ℝ)`, `(hB : ∀ m, 0 ≤ B m)`, and `B m` wherever the original had `B` under the
`∀ m`.  The proof bodies are the originals, unchanged except for `hB m` in place of `hB`.

**One hypothesis is repaired, not copied.**  `CutVarianceLight`'s `hK : ∀ m, K m < N (m+1)` is
**unsatisfiable**: at `m = 0` the horizon is `numStepsAdopted2 1 = ⌈16·1·log 1⌉₊ = 0`, and no
natural number is below `0`.  Both declarations below therefore carry
`hK : ∀ m, Threshold2.n₁ ≤ m → K m < N (m+1)`, which is the only place the proof body uses it
(`stateSupplyR3B_of_cut_light` applies `hK` twice, both inside `intro m hm`).

Sources (all frozen, none edited): `Theorem2R4.lean:73,83,105,124,146,160`,
`StateSupplyBypass.lean:42`, `CutVarianceLight.lean:31,108`.
-/
import Submission.L10.CutVarianceLight
import Submission.L10.StateSupplyBypass

set_option linter.unusedSectionVars false

namespace Submission.L10.Theorem2R5

open MeasureTheory Matrix Finset Module
open scoped ENNReal NNReal RealInnerProductSpace
open Submission.L10 Submission.L10.Increments Submission.L10.Tiling
open Submission.L10.Assembly Submission.L10.ChainDataInst
open Submission.L10.ConstructionA Submission.L10.RawDataInst2
open Submission.L10.RawDataInst2RW2
open Submission.L10.WindowR2 Submission.L10.ChainSetup
open Submission.L10.DriftStopped8R5 Submission.L10.Theorem2R3
open Submission.L10.GoodPathLightR2 Submission.L10.TailAtStepR5W2
open Submission.L10.Theorem2R4 Submission.L10.FinalDischarge
open Submission.L10.StoppedChain Submission.L10.DriftStopped
open Submission.L10.DriftAccumulated Submission.L10.PaddedLawSetupRW2
open Submission.L10.TailSideSetup2

/-! ## 1. `ChainDelivers'` over `ChainRaw3`, at a per-dimension terminal coefficient -/

/-- **`Theorem2R4.ChainDelivers'R3` with `B` inside the `∀ m`.** -/
def ChainDelivers'R3B (A : ℝ) (B : ℕ → ℝ) (c₀ : ℝ) : Prop :=
  ∀ m : ℕ, Threshold2.n₁ ≤ m →
    ∃ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p) (Q : ChainRaw3 p (m + 1)),
      ∀ g : Fin (m + 1) → ZMod p, g ≠ 0 →
        (∀ y : Fin (m + 1) → ℤ, y ≠ 0 → ‖toE (m + 1) y‖ ≤ Q.R → y ∉ latZ p (m + 1) g) →
        Theorem2.LightContact (combW A (B m) Q) Q.supp (θ3 A (B m) p m Q.alpha) g →
        Assembly.ChainOutput Q.alpha g c₀

/-- **`Theorem2R4.klartag_packing_of_chain'R3` with `B` inside the `∀ m`** — `paramsProducer3` is
applied at the `m` that `remaining_of_lemma43'` supplies, so it takes `hB m`. -/
theorem klartag_packing_of_chain'R3B {A c₀ : ℝ} {B : ℕ → ℝ} (hc₀ : 0 < c₀) (hA : 0 < A)
    (hB : ∀ m, 0 ≤ B m) (H : ChainDelivers'R3B A B c₀) :
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
  obtain ⟨P, hα, hR, hsupp, hw, hθ⟩ := paramsProducer3 hA (hB m) p m hp hm' Q
  refine ⟨p, hp, hp0, P, fun g hg hfree hlight => ?_⟩
  rw [hα]
  refine h g hg (fun y hy0 hle => hfree y hy0 (by rwa [hR])) ?_
  rwa [hw, hsupp, hθ] at hlight

/-! ## 2. The drift side and the state supply at the per-dimension coefficient -/

/-- **`Theorem2R4.DriftSideW3` with `B` inside the `∀ m`.** -/
def DriftSideW3B (A : ℝ) (B : ℕ → ℝ) (c₀ : ℝ) : Prop :=
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
      Theorem2.LightContact (wComb A (B m) p m α)
        (RawDataInst2RW2.shellR α (m + 1)) (θ3 A (B m) p m α) g →
      Assembly.ChainOutput α g c₀

/-- **`Theorem2R4.StateSupplyAdoptedR3` with `B` inside the `∀ m`.** -/
def StateSupplyAdoptedR3B (A : ℝ) (B : ℕ → ℝ) (c₃ : ℕ → ℝ) (C' : ℝ) : Prop :=
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
      Theorem2.LightContact (wComb A (B m) p m α)
        (RawDataInst2RW2.shellR α (m + 1)) (θ3 A (B m) p m α) g →
      ∃ (A' : EuclideanSpace ℝ (UT (m + 1))) (M : ℝ),
        A' ∈ Chain.kSet (qC α) (windowOfR2 α p m g) ∧
        Discharge.StateBounds (symMat A') (GoodPathBounds.mAt (m + 1) (c₃ (m + 1))) M ∧
        ChainWiring.logDet A' ≤ C' - 4 * Real.log ((m + 1 : ℕ) : ℝ)

/-- **`Theorem2R4.driftSideW3_of_stateSupplyR3` at the `B`-family**; the body is the original. -/
theorem driftSideW3B_of_stateSupplyR3B {A : ℝ} {B : ℕ → ℝ} {c₃ : ℕ → ℝ}
    (hc₃0 : ∀ n, 0 ≤ c₃ n)
    (hc₃ : ∀ n, c₃ n * DriftStopped6.etaAdopted n ≤ 1 / 4) {C' : ℝ}
    (h : StateSupplyAdoptedR3B A B c₃ C') :
    ∃ c₀ : ℝ, 0 < c₀ ∧ DriftSideW3B A B c₀ := by
  refine ⟨Real.exp (-C' / 2), Real.exp_pos _, ?_⟩
  intro m hm p hp hp0 α hα hn hraw hnd hcov g hg hfree hlight
  obtain ⟨A', M, hkSet, hSB, hlog⟩ := h m hm p hp hp0 α hα hn hraw hnd hcov g hg hfree hlight
  have hm0 : m ≠ 0 := by
    have h2 : 2073600 ≤ m := by simpa [Threshold2.n₁] using hm
    omega
  exact DriftStopped8.chainOutput_of_state hm0 hSB hlog
    (avoid_of_casesR2 hα hSB hkSet hcov hfree (bandSideAdoptedR2 hc₃0 hc₃ m hm p α hα g))

/-- **`Theorem2R4.chainDelivers'R3_of_driftSideW3` at the `B`-family.** -/
theorem chainDelivers'R3B_of_driftSideW3B {A c₀ : ℝ} {B : ℕ → ℝ} (hd : DriftSideW3B A B c₀) :
    ChainDelivers'R3B A B c₀ := by
  intro m hm
  obtain ⟨p, hp, hp0, α, hα, hn, hraw, hnd, hcov⟩ := LatticeDataRW2.rawData_exists'R m hm
  exact ⟨p, hp, hp0, QOf hn hraw hnd,
    fun g hg hfree hlight => hd m hm p hp hp0 α hα hn hraw hnd hcov g hg hfree hlight⟩

/-! ## 3. The bypass and the closing line -/

/-- **`StateSupplyBypass.klartag_packing_of_stateSupplyR3` at the `B`-family.** -/
theorem klartag_packing_of_stateSupplyR3B {A : ℝ} {B : ℕ → ℝ} (hA : 0 < A)
    (hB : ∀ m, 0 ≤ B m) {C' : ℝ} (h : StateSupplyAdoptedR3B A B c3clamp C') :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      let V := EuclideanSpace ℝ (Fin (n + 1))
      ∃ φ : V →ₗ[ℝ] V, let E := φ '' Metric.ball (0 : V) 1
        (MeasureTheory.volume E : EReal) = c * n ^ 2 ∧
        {v ∈ E | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} := by
  obtain ⟨c₀, hc₀, hd⟩ :=
    driftSideW3B_of_stateSupplyR3B c3clamp_nonneg c3clamp_eta_le h
  exact klartag_packing_of_chain'R3B hc₀ hA hB (chainDelivers'R3B_of_driftSideW3B hd)

/-- **`CutVarianceLight.stateSupplyR3_of_cut_light` at the `B`-family**; the body is the original,
which never mentions `A` or `B`. -/
theorem stateSupplyR3B_of_cut_light {A C' : ℝ} {B : ℕ → ℝ} {K : ℕ → ℕ}
    (hK : ∀ m, Threshold2.n₁ ≤ m → K m < ParamsAdopted2.numStepsAdopted2 (m + 1))
    (hline : ∀ m : ℕ, Threshold2.n₁ ≤ m → ∀ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p)
      (α : ℝ), 0 < α → 3 ≤ m + 1 →
      ∀ (_hraw : RawDataR p (m + 1) α ((1 - 1 / ((m + 1 : ℕ) : ℝ)) / α)
          (qC α) (shellR α (m + 1)) (A0C (m + 1)))
        (_hnd : NormData (m + 1) α (qC α) (shellR α (m + 1)) (A0C (m + 1)))
        (g : Fin (m + 1) → ZMod p),
      Theorem2.LightContact (wComb A (B m) p m α) (shellR α (m + 1)) (θ3 A (B m) p m α) g →
      ∃ S pcnt L s : ℝ,
        (S ≤ ∑ k ∈ Finset.range (K m), ∫ ω,
          DriftStopped6.stoppedFreeDim (qC α) (windowOfR2 α p m g) (A0C (m + 1))
            (ChainSetup.step (Submission.L10.cAdopted (m + 1)))
            (DriftStopped6.etaAdopted (m + 1)) (DriftStopped6.r0Adopted (m + 1))
            (DriftStopped6c.c3Adopted'' (m + 1)) (ParamsAdopted2.numStepsAdopted2 (m + 1)) k ω
          ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT (m + 1))))) ∧
        ((ChainSetup.gaussPath (EuclideanSpace ℝ (UT (m + 1)))).real
          (StateInvariant4.countGood (qC α) (windowOfR2 α p m g) (A0C (m + 1))
            (ChainSetup.step (Submission.L10.cAdopted (m + 1))) (K m)
            (DriftStopped6c.c3Adopted'' (m + 1)))ᶜ ≤ pcnt) ∧
        (∫ ω, max (L - stoppedLogDet (qC α) (windowOfR2 α p m g) (A0C (m + 1))
            (ChainSetup.step (Submission.L10.cAdopted (m + 1)))
            (DriftStopped6.etaAdopted (m + 1)) (DriftStopped6.r0Adopted (m + 1))
            (DriftStopped6c.c3Adopted'' (m + 1))
            (ParamsAdopted2.numStepsAdopted2 (m + 1)) (K m) ω) 0
          ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT (m + 1)))) ≤ s) ∧
        L < C' - 4 * Real.log ((m + 1 : ℕ) : ℝ) ∧
        (driftRHS_acc (m + 1) (A0C (m + 1)) (DriftStopped6c.c3Adopted'' (m + 1))
              (EaccAt (m + 1) (DriftStopped6c.c3Adopted'' (m + 1))) S - L + s)
            / ((C' - 4 * Real.log ((m + 1 : ℕ) : ℝ)) - L)
          + GoodPathBounds.failTotal (m + 1) pcnt < 1) :
    StateSupplyAdoptedR3B A B c3clamp C' := by
  intro m hm p hp hp0 α hα hn hraw hnd _hcov g hg _hfree hlight
  have hm1 : 2073600 ≤ m + 1 := by
    have h2 : 2073600 ≤ m := by simpa [Threshold2.n₁] using hm
    omega
  have hN : 1 ≤ ParamsAdopted2.numStepsAdopted2 (m + 1) := by
    have := hK m hm; omega
  obtain ⟨S, pcnt, L, s, hS, hcnt, hshort, hLb, hbudget⟩ :=
    hline m hm p hp hp0 α hα hn hraw hnd g hlight
  have hclamp : c3clamp (m + 1) = DriftStopped6c.c3Adopted'' (m + 1) := c3clamp_eq hm1
  have hc₃0 := DriftStopped6c.c3Adopted''_nonneg (m + 1)
  have hc₃η := DriftStopped6c.c3Adopted''_eta_le hm1
  have hlt := GoodPathBounds.lt_a0C_of_mAt hm1 hc₃η
  have hδ1 : DriftStopped6c.c3Adopted'' (m + 1) * DriftStopped6.etaAdopted (m + 1)
      < a0C (m + 1) - (DriftStopped6.r0Adopted (m + 1)
        + DriftStopped6c.c3Adopted'' (m + 1) * DriftStopped6.etaAdopted (m + 1)) := by
    have hhalf := GoodPathBounds.half_le_mAt hm1 hc₃η
    rw [GoodPathBounds.mAt] at hhalf
    linarith
  have hεnn : (0 : ℝ) ≤ EaccAt (m + 1) (DriftStopped6c.c3Adopted'' (m + 1)) := by
    rw [EaccAt_eq]
    have hm0 : (0 : ℝ) < GoodPathBounds.mAt (m + 1) (DriftStopped6c.c3Adopted'' (m + 1)) := by
      have := GoodPathBounds.half_le_mAt hm1 hc₃η; linarith
    have := DriftStopped7.etaAdopted_nonneg (n := m + 1)
    positivity
  rw [hclamp]
  exact CutVariance.stateTriple_of_cut_var (q := qC α) (W := windowOfR2 α p m g)
    (A₀ := A0C (m + 1)) (r := 1) (K := K m) (ε := EaccAt (m + 1) _) (E := EaccAt (m + 1) _)
    hm1 one_pos (hK m hm) hc₃0 hc₃η
    (kSet_A0C_win hα hn) (hq_win hα hn) (hne_win hα hn) (StateSupply.symMat_A0C (m + 1))
    hεnn
    (ChainErrBudget.stoppedErrBudget_of_params (xs := xOf α)
      (W := windowOfR2 α p m g) (A₀ := A0C (m + 1))
      (ξ := ChainSetup.step (Submission.L10.cAdopted (m + 1))) hN
      (kSet_A0C_win hα hn) (StateSupply.symMat_A0C (m + 1))
      (DriftStopped7.etaAdopted_nonneg (n := m + 1))
      (DriftStopped7.r0Adopted_nonneg (n := m + 1)) hc₃0 hlt hδ1)
    (fun ω J hJ => sum_chainErr_le_c3 (xs := xOf α)
      (W := windowOfR2 α p m g) (A₀ := A0C (m + 1))
      (ξ := ChainSetup.step (Submission.L10.cAdopted (m + 1)))
      (kSet_A0C_win hα hn) (StateSupply.symMat_A0C (m + 1))
      (DriftStopped7.etaAdopted_nonneg (n := m + 1))
      (DriftStopped7.r0Adopted_nonneg (n := m + 1)) hc₃0 hlt hδ1 hJ)
    hS hcnt hshort hLb hbudget

/-- **`CutVarianceLight.klartag_packing_final_light` at the `B`-family** — the challenge statement
from a light-carrying per-line bundle whose terminal coefficient depends on the dimension. -/
theorem klartag_packing_final_lightB {A : ℝ} {B : ℕ → ℝ} (hA : 0 < A) (hB : ∀ m, 0 ≤ B m)
    {C' : ℝ} {K : ℕ → ℕ}
    (hK : ∀ m, Threshold2.n₁ ≤ m → K m < ParamsAdopted2.numStepsAdopted2 (m + 1))
    (hline : ∀ m : ℕ, Threshold2.n₁ ≤ m → ∀ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p)
      (α : ℝ), 0 < α → 3 ≤ m + 1 →
      ∀ (_hraw : RawDataR p (m + 1) α ((1 - 1 / ((m + 1 : ℕ) : ℝ)) / α)
          (qC α) (shellR α (m + 1)) (A0C (m + 1)))
        (_hnd : NormData (m + 1) α (qC α) (shellR α (m + 1)) (A0C (m + 1)))
        (g : Fin (m + 1) → ZMod p),
      Theorem2.LightContact (wComb A (B m) p m α) (shellR α (m + 1)) (θ3 A (B m) p m α) g →
      ∃ S pcnt L s : ℝ,
        (S ≤ ∑ k ∈ Finset.range (K m), ∫ ω,
          DriftStopped6.stoppedFreeDim (qC α) (windowOfR2 α p m g) (A0C (m + 1))
            (ChainSetup.step (Submission.L10.cAdopted (m + 1)))
            (DriftStopped6.etaAdopted (m + 1)) (DriftStopped6.r0Adopted (m + 1))
            (DriftStopped6c.c3Adopted'' (m + 1)) (ParamsAdopted2.numStepsAdopted2 (m + 1)) k ω
          ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT (m + 1))))) ∧
        ((ChainSetup.gaussPath (EuclideanSpace ℝ (UT (m + 1)))).real
          (StateInvariant4.countGood (qC α) (windowOfR2 α p m g) (A0C (m + 1))
            (ChainSetup.step (Submission.L10.cAdopted (m + 1))) (K m)
            (DriftStopped6c.c3Adopted'' (m + 1)))ᶜ ≤ pcnt) ∧
        (∫ ω, max (L - stoppedLogDet (qC α) (windowOfR2 α p m g) (A0C (m + 1))
            (ChainSetup.step (Submission.L10.cAdopted (m + 1)))
            (DriftStopped6.etaAdopted (m + 1)) (DriftStopped6.r0Adopted (m + 1))
            (DriftStopped6c.c3Adopted'' (m + 1))
            (ParamsAdopted2.numStepsAdopted2 (m + 1)) (K m) ω) 0
          ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT (m + 1)))) ≤ s) ∧
        L < C' - 4 * Real.log ((m + 1 : ℕ) : ℝ) ∧
        (driftRHS_acc (m + 1) (A0C (m + 1)) (DriftStopped6c.c3Adopted'' (m + 1))
              (EaccAt (m + 1) (DriftStopped6c.c3Adopted'' (m + 1))) S - L + s)
            / ((C' - 4 * Real.log ((m + 1 : ℕ) : ℝ)) - L)
          + GoodPathBounds.failTotal (m + 1) pcnt < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      let V := EuclideanSpace ℝ (Fin (n + 1))
      ∃ φ : V →ₗ[ℝ] V, let E := φ '' Metric.ball (0 : V) 1
        (MeasureTheory.volume E : EReal) = c * n ^ 2 ∧
        {v ∈ E | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} :=
  klartag_packing_of_stateSupplyR3B hA hB (stateSupplyR3B_of_cut_light hK hline)

end Submission.L10.Theorem2R5

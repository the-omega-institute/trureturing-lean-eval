import Submission.L10.GoodPathLightR2
import Submission.L10.DriftStopped6b
import Submission.L10.FreeDimTotal
import Submission.L10.Theorem2R3

/-!
# Gate L-10 (`klartag_packing`) — the drift side at `windowOfR2`, and `LightGoodPath2`

Brief 82a's continuation.  Report 85c §2 found that `GoodPathBounds.goodPathAt_of_S` cannot be
re-used at the generic reach window, because `Chain.kSet` is **antitone** in the window.  The
general theorem `GoodPathBounds.goodPathAt` *is* reusable — it is stated for an arbitrary `q W A₀`
— so this module is the substitution pass: the chain data on `windowOfR2` comes from
`RawDataInst2RW2.lattice_fieldsR`, which needs only `0 < α` and `3 ≤ m+1` and **not** `RawDataR`,
so `LightGoodPath2`'s binders suffice.

## Contents

* `hq_win`, `hne_win`, `kSet_A0C_win` — the chain's three data hypotheses on `windowOfR2`, from
  `lattice_fieldsR` through `DriftStopped8R5.windowOfR2_subset`.
* `sum_lt_of_lightContact2` — `GoodPathLight.sum_lt_of_lightContact` at the reach-2 shell, through
  `DriftStopped8R5.filter_eq_windowOfR2` (rule 16).
* `goodPathAt2_of_inputs` — `GoodPathBounds.goodPathAt` packaged as
  `GoodPathLightR2.GoodPathAt2`.
* `lightGoodPath2_of_inputs`, `klartag_packing_final'''` — the composition, with the inputs that
  are still owed upstream carried as named hypotheses rather than assumed away.

`GoodPathBounds`, `FreeDimTotal`, `GoodPathLightR2`, `DriftStopped6b`, `Theorem2R3` are reported
and are not edited; this module imports them.
-/

set_option linter.unusedSectionVars false

namespace Submission.L10.FinalDischarge

open MeasureTheory Matrix Finset Module Submission.L10 Submission.L10.Increments
open Submission.L10.StoppedChain Submission.L10.DriftStopped Submission.L10.DriftStopped5
open Submission.L10.DriftInputsStopped Submission.L10.GoodPathBounds
open Submission.L10.ConstructionA Submission.L10.Tiling
open Submission.L10.RawDataInst2RW2 Submission.L10.RawDataInst2
open Submission.L10.DriftStopped8R5 Submission.L10.GoodPathLightR2
open scoped ENNReal NNReal RealInnerProductSpace

/-! ## 1. The chain's data on `windowOfR2`, with no `RawDataR` -/

section Data

variable {p m : ℕ} {α : ℝ} {g : Fin (m + 1) → ZMod p}

theorem hq_win (hα : 0 < α) (hn : 3 ≤ m + 1) :
    ∀ i ∈ windowOfR2 α p m g, ∀ j ∈ windowOfR2 α p m g,
      (0 : ℝ) ≤ ⟪qC α i, qC α j⟫ :=
  fun i hi _ _ => (lattice_fieldsR hα hn).1 _ i (windowOfR2_subset hi)

theorem hne_win (hα : 0 < α) (hn : 3 ≤ m + 1) :
    ∀ i ∈ windowOfR2 α p m g, qC α i ≠ 0 := by
  intro y hy
  have hr := (lattice_fieldsR hα hn).2.2.2.2.2.1 y (windowOfR2_subset hy)
  have hnorm : ‖qC α y‖ = (α * ‖toE (m + 1) y‖) ^ 2 := norm_qC α y
  intro hzero
  rw [hzero, norm_zero] at hnorm
  nlinarith [hr, hnorm]

theorem kSet_A0C_win (hα : 0 < α) (hn : 3 ≤ m + 1) :
    A0C (m + 1) ∈ Chain.kSet (qC α) (windowOfR2 α p m g) :=
  fun y hy => le_of_lt ((lattice_fieldsR hα hn).2.1 y (windowOfR2_subset hy))

end Data

/-! ## 2. The light contact on the reach-2 window -/

section Light

variable {p m : ℕ} [NeZero p] {α : ℝ} {g : Fin (m + 1) → ZMod p}

/-- `GoodPathLight.sum_lt_of_lightContact` at the reach-2 shell; the index set moves by
`DriftStopped8R5.filter_eq_windowOfR2` (rule 16 — the two `open Classical` filters of
`· ∈ latZ p (m+1) g` are not the same term). -/
theorem sum_lt_of_lightContact2 {v : (Fin (m + 1) → ℤ) → ℝ} {Θ : ℝ}
    (hv : ∀ y, 0 ≤ v y) (hΘ : 0 < Θ)
    (h : Theorem2.LightContact (fun y => ENNReal.ofReal (v y))
      (RawDataInst2RW2.shellR α (m + 1)) (ENNReal.ofReal Θ) g) :
    ∑ y ∈ windowOfR2 α p m g, v y < Θ := by
  classical
  have h' : ∑ y ∈ (RawDataInst2RW2.shellR α (m + 1)).filter
      (fun y => y ∈ latZ p (m + 1) g), ENNReal.ofReal (v y) < ENNReal.ofReal Θ := h
  rw [filter_eq_windowOfR2] at h'
  rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ => hv y)] at h'
  exact (ENNReal.ofReal_lt_ofReal_iff hΘ).1 h'

end Light

/-! ## 3. `GoodPathAt2` from the drift side -/

section Path

variable {p m : ℕ} {α C' : ℝ} {g : Fin (m + 1) → ZMod p}

/-- **`GoodPathBounds.goodPathAt` at `windowOfR2`.**  Report 85c §2: the *specialised*
`goodPathAt_of_S` cannot be re-used because `Chain.kSet` is antitone in the window, but the general
`goodPathAt` can, and §1 supplies its three data hypotheses without `RawDataR`. -/
theorem goodPathAt2_of_inputs (hm : Threshold2.n₁ ≤ m) (hα : 0 < α)
    {c₃ ε S pcnt : ℝ} (hc₃0 : 0 ≤ c₃)
    (hc₃η : c₃ * DriftStopped6.etaAdopted (m + 1) ≤ 1 / 4) (hε : 0 ≤ ε)
    (hbdabs : ∀ ω, ∀ k, |ChainWiring.chainErr (qC α) (windowOfR2 α p m g) (A0C (m + 1))
      (ChainSetup.step (Submission.L10.cAdopted (m + 1))) k ω| ≤ ε)
    (hS : S ≤ ∑ k ∈ Finset.range (ParamsAdopted2.numStepsAdopted2 (m + 1) - 1), ∫ ω,
      DriftStopped6.stoppedFreeDim (qC α) (windowOfR2 α p m g) (A0C (m + 1))
        (ChainSetup.step (Submission.L10.cAdopted (m + 1)))
        (DriftStopped6.etaAdopted (m + 1)) (DriftStopped6.r0Adopted (m + 1)) c₃
        (ParamsAdopted2.numStepsAdopted2 (m + 1)) k ω
      ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT (m + 1)))))
    (hcnt : (ChainSetup.gaussPath (EuclideanSpace ℝ (UT (m + 1)))).real
        (StateInvariant4.countGood (qC α) (windowOfR2 α p m g) (A0C (m + 1))
          (ChainSetup.step (Submission.L10.cAdopted (m + 1)))
          (ParamsAdopted2.numStepsAdopted2 (m + 1)) c₃)ᶜ ≤ pcnt)
    (hLb : logDetLow (m + 1) c₃ < C' - 4 * Real.log ((m + 1 : ℕ) : ℝ))
    (hbudget : (driftRHS (m + 1) (A0C (m + 1)) c₃ ε S - logDetLow (m + 1) c₃)
        / ((C' - 4 * Real.log ((m + 1 : ℕ) : ℝ)) - logDetLow (m + 1) c₃)
      + failTotal (m + 1) pcnt < 1) :
    GoodPathAt2 p m α g c₃ C' := by
  have hm1 : 2073600 ≤ m + 1 := by
    have h2 : 2073600 ≤ m := by simpa [Threshold2.n₁] using hm
    omega
  have hn3 : 3 ≤ m + 1 := by omega
  have hN : 1 ≤ ParamsAdopted2.numStepsAdopted2 (m + 1) := by
    have := Submission.L10.three_le_numStepsAdopted2 (n := m + 1) (by omega); omega
  obtain ⟨ω, hω, hlog⟩ := goodPathAt (q := qC α) (W := windowOfR2 α p m g)
    (A₀ := A0C (m + 1)) (r := 1) hm1 one_pos hc₃0 hc₃η
    (kSet_A0C_win hα hn3) (hq_win hα hn3) (hne_win hα hn3)
    (StateSupply.symMat_A0C (m + 1)) hε hbdabs hS hcnt hLb hbudget
  exact ⟨1, 6 * 1 * 1 * Real.sqrt ((m + 1 : ℕ) : ℝ), ChainSetup.coord 0,
    ParamsAdopted2.numStepsAdopted2 (m + 1) - 1, ω, by omega, hω, hlog⟩

end Path

/-! ## 4. `LightGoodPath2`, and the challenge statement -/

section Final

variable {c₃ : ℕ → ℝ} {θ : ℕ → ℕ → ℝ → ℝ≥0∞} {C' : ℝ}

/-- **`LightGoodPath2` from the per-line drift inputs.**  The light contact and the R-condition are
**carried into** `hline`, not dropped: whoever discharges the four numeric inputs has both in hand.
That is the shape report 82b's §0 says this lane has got wrong three times. -/
theorem lightGoodPath2_of_inputs (hc₃0 : ∀ n, 0 ≤ c₃ n)
    (hc₃η : ∀ n, c₃ n * DriftStopped6.etaAdopted n ≤ 1 / 4)
    (hline : ∀ m : ℕ, Threshold2.n₁ ≤ m → ∀ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p)
      (α : ℝ), 0 < α → ∀ g : Fin (m + 1) → ZMod p, g ≠ 0 →
      (∀ y : Fin (m + 1) → ℤ, y ≠ 0 →
        ‖toE (m + 1) y‖ ≤ (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α → y ∉ latZ p (m + 1) g) →
      Theorem2.LightContact (Theorem2R3.wR2 p m α) (RawDataInst2RW2.shellR α (m + 1))
        (θ p m α) g →
      ∃ ε S pcnt : ℝ, 0 ≤ ε ∧
        (∀ ω, ∀ k, |ChainWiring.chainErr (qC α) (windowOfR2 α p m g) (A0C (m + 1))
          (ChainSetup.step (Submission.L10.cAdopted (m + 1))) k ω| ≤ ε) ∧
        (S ≤ ∑ k ∈ Finset.range (ParamsAdopted2.numStepsAdopted2 (m + 1) - 1), ∫ ω,
          DriftStopped6.stoppedFreeDim (qC α) (windowOfR2 α p m g) (A0C (m + 1))
            (ChainSetup.step (Submission.L10.cAdopted (m + 1)))
            (DriftStopped6.etaAdopted (m + 1)) (DriftStopped6.r0Adopted (m + 1)) (c₃ (m + 1))
            (ParamsAdopted2.numStepsAdopted2 (m + 1)) k ω
          ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT (m + 1))))) ∧
        ((ChainSetup.gaussPath (EuclideanSpace ℝ (UT (m + 1)))).real
          (StateInvariant4.countGood (qC α) (windowOfR2 α p m g) (A0C (m + 1))
            (ChainSetup.step (Submission.L10.cAdopted (m + 1)))
            (ParamsAdopted2.numStepsAdopted2 (m + 1)) (c₃ (m + 1)))ᶜ ≤ pcnt) ∧
        logDetLow (m + 1) (c₃ (m + 1)) < C' - 4 * Real.log ((m + 1 : ℕ) : ℝ) ∧
        (driftRHS (m + 1) (A0C (m + 1)) (c₃ (m + 1)) ε S - logDetLow (m + 1) (c₃ (m + 1)))
            / ((C' - 4 * Real.log ((m + 1 : ℕ) : ℝ)) - logDetLow (m + 1) (c₃ (m + 1)))
          + failTotal (m + 1) pcnt < 1) :
    LightGoodPath2 c₃ Theorem2R3.wR2 θ C' := by
  intro m hm p hp hp0 α hα g hg hfree hlight
  obtain ⟨ε, S, pcnt, hε, hbdabs, hS, hcnt, hLb, hbudget⟩ :=
    hline m hm p hp hp0 α hα g hg hfree hlight
  exact goodPathAt2_of_inputs hm hα (hc₃0 (m + 1)) (hc₃η (m + 1)) hε hbdabs hS hcnt hLb hbudget

/-- **The challenge statement**, from the `Params` producer and the per-line drift inputs. -/
theorem klartag_packing_final''' (hc₃0 : ∀ n, 0 ≤ c₃ n)
    (hc₃η : ∀ n, c₃ n * DriftStopped6.etaAdopted n ≤ 1 / 4)
    (hpr : Theorem2R3.ParamsProducerR2 θ)
    (hline : ∀ m : ℕ, Threshold2.n₁ ≤ m → ∀ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p)
      (α : ℝ), 0 < α → ∀ g : Fin (m + 1) → ZMod p, g ≠ 0 →
      (∀ y : Fin (m + 1) → ℤ, y ≠ 0 →
        ‖toE (m + 1) y‖ ≤ (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α → y ∉ latZ p (m + 1) g) →
      Theorem2.LightContact (Theorem2R3.wR2 p m α) (RawDataInst2RW2.shellR α (m + 1))
        (θ p m α) g →
      ∃ ε S pcnt : ℝ, 0 ≤ ε ∧
        (∀ ω, ∀ k, |ChainWiring.chainErr (qC α) (windowOfR2 α p m g) (A0C (m + 1))
          (ChainSetup.step (Submission.L10.cAdopted (m + 1))) k ω| ≤ ε) ∧
        (S ≤ ∑ k ∈ Finset.range (ParamsAdopted2.numStepsAdopted2 (m + 1) - 1), ∫ ω,
          DriftStopped6.stoppedFreeDim (qC α) (windowOfR2 α p m g) (A0C (m + 1))
            (ChainSetup.step (Submission.L10.cAdopted (m + 1)))
            (DriftStopped6.etaAdopted (m + 1)) (DriftStopped6.r0Adopted (m + 1)) (c₃ (m + 1))
            (ParamsAdopted2.numStepsAdopted2 (m + 1)) k ω
          ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT (m + 1))))) ∧
        ((ChainSetup.gaussPath (EuclideanSpace ℝ (UT (m + 1)))).real
          (StateInvariant4.countGood (qC α) (windowOfR2 α p m g) (A0C (m + 1))
            (ChainSetup.step (Submission.L10.cAdopted (m + 1)))
            (ParamsAdopted2.numStepsAdopted2 (m + 1)) (c₃ (m + 1)))ᶜ ≤ pcnt) ∧
        logDetLow (m + 1) (c₃ (m + 1)) < C' - 4 * Real.log ((m + 1 : ℕ) : ℝ) ∧
        (driftRHS (m + 1) (A0C (m + 1)) (c₃ (m + 1)) ε S - logDetLow (m + 1) (c₃ (m + 1)))
            / ((C' - 4 * Real.log ((m + 1 : ℕ) : ℝ)) - logDetLow (m + 1) (c₃ (m + 1)))
          + failTotal (m + 1) pcnt < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      let V := EuclideanSpace ℝ (Fin (n + 1))
      ∃ φ : V →ₗ[ℝ] V, let E := φ '' Metric.ball (0 : V) 1
        (MeasureTheory.volume E : EReal) = c * n ^ 2 ∧
        {v ∈ E | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} :=
  klartag_packing_of_lightGoodPath2 hc₃0 hc₃η hpr
    (lightGoodPath2_of_inputs hc₃0 hc₃η hline)

end Final

end Submission.L10.FinalDischarge

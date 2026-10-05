/-
Gate L-10 (`klartag_packing`), brief 95 item (5) — `StateSupplyAdoptedR3` from a per-line bundle
that **keeps the binder's light contact**.

`CutVariance.stateSupplyR3_of_cut_var` discards `hlight`, `hraw` and `hnd` (they appear as `_hcov`,
`_hfree`, `_hlight` in its `intro` pattern), so its `hline` has to hold for *every* `p`, `α`, `g` —
which no tail-side theorem can supply, since `TailWiring.hS_light_win` and `hcnt_win` both consume
the light contact.  This is the same statement with those three passed through to `hline`.  The
proof body is `stateSupplyR3_of_cut_var`'s, unchanged.

Nothing reported is edited.
-/
import Submission.L10.CutVariance
import Submission.L10.TailWiring

set_option linter.unusedSectionVars false

namespace Submission.L10.CutVarianceLight

open MeasureTheory Matrix Finset Module
open scoped ENNReal RealInnerProductSpace
open Submission.L10 Submission.L10.Increments Submission.L10.StoppedChain
open Submission.L10.DriftStopped Submission.L10.Theorem2R4
open Submission.L10.RawDataInst2 Submission.L10.RawDataInst2RW2
open Submission.L10.ConstructionA Submission.L10.Tiling
open Submission.L10.DriftStopped8R5 Submission.L10.FinalDischarge
open Submission.L10.DriftAccumulated Submission.L10.PaddedLawSetupRW2
open Submission.L10.TailSideSetup2

/-- **`StateSupplyAdoptedR3` from a light-carrying per-line bundle.** -/
theorem stateSupplyR3_of_cut_light {A B C' : ℝ} {K : ℕ → ℕ}
    (hK : ∀ m, K m < ParamsAdopted2.numStepsAdopted2 (m + 1))
    (hline : ∀ m : ℕ, Threshold2.n₁ ≤ m → ∀ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p)
      (α : ℝ), 0 < α → 3 ≤ m + 1 →
      ∀ (_hraw : RawDataR p (m + 1) α ((1 - 1 / ((m + 1 : ℕ) : ℝ)) / α)
          (qC α) (shellR α (m + 1)) (A0C (m + 1)))
        (_hnd : NormData (m + 1) α (qC α) (shellR α (m + 1)) (A0C (m + 1)))
        (g : Fin (m + 1) → ZMod p),
      Theorem2.LightContact (wComb A B p m α) (shellR α (m + 1)) (θ3 A B p m α) g →
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
    StateSupplyAdoptedR3 A B c3clamp C' := by
  intro m hm p hp hp0 α hα hn hraw hnd _hcov g hg _hfree hlight
  have hm1 : 2073600 ≤ m + 1 := by
    have h2 : 2073600 ≤ m := by simpa [Threshold2.n₁] using hm
    omega
  have hN : 1 ≤ ParamsAdopted2.numStepsAdopted2 (m + 1) := by
    have := hK m; omega
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
    hm1 one_pos (hK m) hc₃0 hc₃η
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

/-- **The challenge statement**, from the light-carrying bundle. -/
theorem klartag_packing_final_light {A B : ℝ} (hA : 0 < A) (hB : 0 ≤ B) {C' : ℝ} {K : ℕ → ℕ}
    (hK : ∀ m, K m < ParamsAdopted2.numStepsAdopted2 (m + 1))
    (hline : ∀ m : ℕ, Threshold2.n₁ ≤ m → ∀ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p)
      (α : ℝ), 0 < α → 3 ≤ m + 1 →
      ∀ (_hraw : RawDataR p (m + 1) α ((1 - 1 / ((m + 1 : ℕ) : ℝ)) / α)
          (qC α) (shellR α (m + 1)) (A0C (m + 1)))
        (_hnd : NormData (m + 1) α (qC α) (shellR α (m + 1)) (A0C (m + 1)))
        (g : Fin (m + 1) → ZMod p),
      Theorem2.LightContact (wComb A B p m α) (shellR α (m + 1)) (θ3 A B p m α) g →
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
  StateSupplyBypass.klartag_packing_of_stateSupplyR3 hA hB
    (stateSupplyR3_of_cut_light hK hline)

end Submission.L10.CutVarianceLight

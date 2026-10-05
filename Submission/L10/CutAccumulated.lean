import Submission.L10.DriftAccumulated
import Submission.L10.StateSupplyBypass

/-!
# Gate L-10 (`klartag_packing`) — brief 93's accumulated total, at the **cut** count index

Report `90-step-c-target.md`: `GoodPathBounds.GoodPathAt` and `GoodPathLightR2.GoodPathAt2` read
`countGood` at the horizon `N`, and the tail side bounds `P.real {y ∈ C_k}` only for `k < N`
(`ChainWalkRW2.hsteps_of_walkRW2`, `TailAtStepR5W2.terminal_le_wProfT` at `k = N − 1`).  So brief
93's `goodPathAt_acc` — whose `hcnt` is at `N` — cannot be fed from the tail side either.

The repair is one index.  `GoodPathBounds.goodCut … K` reads the count at `K`; at `K = N − 1` the
drift horizon is `N − 1` as well, so the loss is one step out of `N = ⌈16 n⁷ log n⌉`.  This module
is `DriftAccumulated.goodPathAt_acc` at `goodCut … K`, and then
`Theorem2R4.StateSupplyAdoptedR3` through `GoodPathBounds.stateTriple_of_cut`'s route.

**Both freeze budgets are proved, not assumed**: `ChainErrBudget.stoppedErrBudget_of_params` and
`DriftAccumulated.sum_chainErr_le_c3`, at `ε = E = DriftAccumulated.EaccAt n c₃`.

`DriftAccumulated.lean`, `ChainErrBudget.lean`, `GoodPathBounds.lean`, `StateSupplyBypass.lean`
and `Theorem2R4.lean` are reported and are not edited.
-/

set_option linter.unusedSectionVars false

namespace Submission.L10.CutAccumulated

open MeasureTheory Matrix Finset Module Submission.L10 Submission.L10.Increments
open Submission.L10.StoppedChain Submission.L10.DriftStopped Submission.L10.DriftStopped5
open Submission.L10.DriftInputsStopped Submission.L10.GoodPathBounds
open Submission.L10.DriftAccumulated
open scoped NNReal RealInnerProductSpace

section Cut

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}

/-- **`DriftAccumulated.goodPathAt_acc` with the count read at `K < N`.** -/
theorem goodPathCut_acc (hn : 2073600 ≤ n) {c₃ ε E S b pcnt r : ℝ} {K : ℕ} (hr : 0 < r)
    (hKN : K < ParamsAdopted2.numStepsAdopted2 n)
    (hc₃0 : 0 ≤ c₃) (hc₃η : c₃ * DriftStopped6.etaAdopted n ≤ 1 / 4)
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a0C n • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hε : 0 ≤ ε)
    (hbdabs : ChainErrBudget.StoppedErrBudget q W A₀
      (ChainSetup.step (Submission.L10.cAdopted n)) (DriftStopped6.etaAdopted n)
      (DriftStopped6.r0Adopted n) c₃ (ParamsAdopted2.numStepsAdopted2 n) ε)
    (hpre : ∀ ω, ∀ J, J < tau q W A₀ (ChainSetup.step (Submission.L10.cAdopted n))
        (DriftStopped6.etaAdopted n) (DriftStopped6.r0Adopted n) c₃
        (ParamsAdopted2.numStepsAdopted2 n) ω →
      ∑ k ∈ Finset.range J, ChainWiring.chainErr q W A₀
        (ChainSetup.step (Submission.L10.cAdopted n)) k ω ≤ E)
    (hS : S ≤ ∑ k ∈ Finset.range K, ∫ ω,
      DriftStopped6.stoppedFreeDim q W A₀ (ChainSetup.step (Submission.L10.cAdopted n))
        (DriftStopped6.etaAdopted n) (DriftStopped6.r0Adopted n) c₃
        (ParamsAdopted2.numStepsAdopted2 n) k ω
      ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))))
    (hcnt : (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))).real
        (StateInvariant4.countGood q W A₀ (ChainSetup.step (Submission.L10.cAdopted n))
          K c₃)ᶜ ≤ pcnt)
    (hLb : GoodPathBounds.logDetLow n c₃ < b)
    (hbudget : (driftRHS_acc n A₀ c₃ E S - GoodPathBounds.logDetLow n c₃)
        / (b - GoodPathBounds.logDetLow n c₃)
      + GoodPathBounds.failTotal n pcnt < 1) :
    ∃ ω, ω ∈ GoodPathBounds.goodCut r (ChainSetup.coord 0)
        (ChainSetup.step (Submission.L10.cAdopted n)) (6 * r * 1 * Real.sqrt n)
        (ParamsAdopted2.numStepsAdopted2 n) (DriftStopped6.etaAdopted n) q W A₀
        (DriftStopped6.r0Adopted n) c₃ K ∧
      ChainWiring.logDet (Chain.chain q W A₀
        (ChainSetup.step (Submission.L10.cAdopted n)) K ω).1 ≤ b := by
  have hn3 : 3 ≤ n := by omega
  have hN : 1 ≤ ParamsAdopted2.numStepsAdopted2 n := by omega
  have hξm : ∀ j, Measurable (ChainSetup.step (ι := UT n) (Submission.L10.cAdopted n) j) :=
    fun j => ChainSetup.measurable_step _ j
  have hG : ∀ k, MeasurableSet[ChainSetup.filtration (F := EuclideanSpace ℝ (UT n)) k]
      (stateGood q W A₀ (ChainSetup.step (Submission.L10.cAdopted n))
        (DriftStopped6.etaAdopted n) (DriftStopped6.r0Adopted n) c₃ k) :=
    fun k => measurableSet_stateGood_step _ _ _ _ k
  have hτ : Measurable (tau q W A₀ (ChainSetup.step (Submission.L10.cAdopted n))
      (DriftStopped6.etaAdopted n) (DriftStopped6.r0Adopted n) c₃
      (ParamsAdopted2.numStepsAdopted2 n)) :=
    DriftStopped5.measurable_tau (ChainSetup.filtration (F := EuclideanSpace ℝ (UT n))) hG _
  have hlt := GoodPathBounds.lt_a0C_of_mAt hn hc₃η
  have hinterr := fun k => ChainErrBudget.integrable_stoppedErr_of_stopped
    (q := q) (W := W) (A₀ := A₀) (cq := GoodPathBounds.cqAt n c₃) (ε := ε) hN hA₀ hq hne hA₀m
    (DriftStopped7.etaAdopted_nonneg (n := n)) (DriftStopped7.r0Adopted_nonneg (n := n))
    hc₃0 hlt (GoodPathBounds.cqAt_nonneg hn hc₃η hc₃0) hε hτ hbdabs k
  have hdrift := drift_bound_at_acc (q := q) (W := W) (A₀ := A₀) (m := K)
    hn hc₃0 hc₃η hA₀ hq hne hA₀m hinterr hS hpre
  have hzero : ∫ ω, stoppedLogDet q W A₀ (ChainSetup.step (Submission.L10.cAdopted n))
        (DriftStopped6.etaAdopted n) (DriftStopped6.r0Adopted n) c₃
        (ParamsAdopted2.numStepsAdopted2 n) 0 ω
        ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))
      = ChainWiring.logDet A₀ := by
    simp only [GoodPathBounds.stoppedLogDet_zero]; simp
  rw [hzero] at hdrift
  have hfail : (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))).real
      (GoodPathBounds.goodCut r (ChainSetup.coord 0)
        (ChainSetup.step (Submission.L10.cAdopted n)) (6 * r * 1 * Real.sqrt n)
        (ParamsAdopted2.numStepsAdopted2 n) (DriftStopped6.etaAdopted n) q W A₀
        (DriftStopped6.r0Adopted n) c₃ K)ᶜ ≤ GoodPathBounds.failTotal n pcnt := by
    refine le_trans (GoodPathBounds.measureReal_compl_goodCut_le _ _ _ _ _ _ _ _) ?_
    rw [GoodPathBounds.failTotal]
    have h1 := GoodPathBounds.chainGood_failure (n := n) hn3 hr
    have h2 := GoodPathBounds.accGood_failure (q := q) (W := W) (A₀ := A₀) hn3
    linarith [hcnt]
  obtain ⟨ω, hb, hω⟩ := GoodPathBounds.exists_mem_of_integral_le
    (DriftStopped6.measurable_stoppedLogDet hξm hτ K)
    (DriftStopped6.integrable_stoppedLogDet hN hξm hτ hA₀ hq hne hA₀m
      (DriftStopped7.etaAdopted_nonneg (n := n)) (DriftStopped7.r0Adopted_nonneg (n := n))
      hc₃0 hlt K)
    (L := GoodPathBounds.logDetLow n c₃) (B := driftRHS_acc n A₀ c₃ E S)
    (fun ω => GoodPathBounds.stoppedLogDet_ge hN hA₀ hq hne hA₀m
      (DriftStopped7.etaAdopted_nonneg (n := n)) (DriftStopped7.r0Adopted_nonneg (n := n))
      hc₃0 hlt K ω)
    hdrift
    (GoodPathBounds.measurableSet_goodCut hξm (ChainSetup.measurable_coord 0) _ _ _ _ _ _ _)
    hfail hLb hbudget
  refine ⟨ω, hω, ?_⟩
  rwa [GoodPathBounds.stoppedLogDet_eq_of_lt_tau
    (GoodPathBounds.lt_tau_of_goodCut hω hKN)] at hb

/-- **The state triple on the accumulated total**, at the cut index. -/
theorem stateTriple_of_cut_acc (hn : 2073600 ≤ n) {c₃ ε E S b pcnt r : ℝ} {K : ℕ} (hr : 0 < r)
    (hKN : K < ParamsAdopted2.numStepsAdopted2 n)
    (hc₃0 : 0 ≤ c₃) (hc₃η : c₃ * DriftStopped6.etaAdopted n ≤ 1 / 4)
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a0C n • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hε : 0 ≤ ε)
    (hbdabs : ChainErrBudget.StoppedErrBudget q W A₀
      (ChainSetup.step (Submission.L10.cAdopted n)) (DriftStopped6.etaAdopted n)
      (DriftStopped6.r0Adopted n) c₃ (ParamsAdopted2.numStepsAdopted2 n) ε)
    (hpre : ∀ ω, ∀ J, J < tau q W A₀ (ChainSetup.step (Submission.L10.cAdopted n))
        (DriftStopped6.etaAdopted n) (DriftStopped6.r0Adopted n) c₃
        (ParamsAdopted2.numStepsAdopted2 n) ω →
      ∑ k ∈ Finset.range J, ChainWiring.chainErr q W A₀
        (ChainSetup.step (Submission.L10.cAdopted n)) k ω ≤ E)
    (hS : S ≤ ∑ k ∈ Finset.range K, ∫ ω,
      DriftStopped6.stoppedFreeDim q W A₀ (ChainSetup.step (Submission.L10.cAdopted n))
        (DriftStopped6.etaAdopted n) (DriftStopped6.r0Adopted n) c₃
        (ParamsAdopted2.numStepsAdopted2 n) k ω
      ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))))
    (hcnt : (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))).real
        (StateInvariant4.countGood q W A₀ (ChainSetup.step (Submission.L10.cAdopted n))
          K c₃)ᶜ ≤ pcnt)
    (hLb : GoodPathBounds.logDetLow n c₃ < b)
    (hbudget : (driftRHS_acc n A₀ c₃ E S - GoodPathBounds.logDetLow n c₃)
        / (b - GoodPathBounds.logDetLow n c₃)
      + GoodPathBounds.failTotal n pcnt < 1) :
    ∃ (A : EuclideanSpace ℝ (UT n)) (M : ℝ), A ∈ Chain.kSet q W ∧
      Discharge.StateBounds (symMat A) (GoodPathBounds.mAt n c₃) M ∧
      ChainWiring.logDet A ≤ b := by
  obtain ⟨ω, hω, hlog⟩ := goodPathCut_acc hn hr hKN hc₃0 hc₃η hA₀ hq hne hA₀m hε hbdabs hpre
    hS hcnt hLb hbudget
  exact ⟨(Chain.chain q W A₀ (ChainSetup.step (Submission.L10.cAdopted n)) K ω).1,
    GoodPathBounds.MAt n c₃, Chain.chain_fst_mem_kSet hA₀ hq hne K ω,
    GoodPathBounds.stateBounds_goodCut hA₀ hq hne hA₀m
      (DriftStopped7.etaAdopted_nonneg (n := n)) (DriftStopped7.r0Adopted_nonneg (n := n))
      hc₃0 (GoodPathBounds.lt_a0C_of_mAt hn hc₃η) hω hKN, hlog⟩

end Cut

/-! ## 2. `StateSupplyAdoptedR3`, with both freeze budgets proved -/

section Supply

open Submission.L10.Theorem2R4 Submission.L10.RawDataInst2 Submission.L10.ConstructionA
open Submission.L10.Tiling Submission.L10.FinalDischarge

/-- **`StateSupplyAdoptedR3` from the cut accumulated triple.**  `ε = E = EaccAt (m+1) c₃''`, and
both budgets are theorems: `ChainErrBudget.stoppedErrBudget_of_params` and
`DriftAccumulated.sum_chainErr_le_c3`.  What is left per line is `hS`, `hcnt` (both from 85f's
`both_sums_windowR2`) and the two numeric facts. -/
theorem stateSupplyR3_of_cut_acc {A B C' : ℝ} {K : ℕ → ℕ}
    (hK : ∀ m, K m < ParamsAdopted2.numStepsAdopted2 (m + 1))
    (hline : ∀ m : ℕ, Threshold2.n₁ ≤ m → ∀ (p : ℕ) (α : ℝ), 0 < α →
      ∀ g : Fin (m + 1) → ZMod p,
      ∃ S pcnt : ℝ,
        (S ≤ ∑ k ∈ Finset.range (K m), ∫ ω,
          DriftStopped6.stoppedFreeDim (qC α) (DriftStopped8R5.windowOfR2 α p m g) (A0C (m + 1))
            (ChainSetup.step (Submission.L10.cAdopted (m + 1)))
            (DriftStopped6.etaAdopted (m + 1)) (DriftStopped6.r0Adopted (m + 1))
            (DriftStopped6c.c3Adopted'' (m + 1)) (ParamsAdopted2.numStepsAdopted2 (m + 1)) k ω
          ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT (m + 1))))) ∧
        ((ChainSetup.gaussPath (EuclideanSpace ℝ (UT (m + 1)))).real
          (StateInvariant4.countGood (qC α) (DriftStopped8R5.windowOfR2 α p m g) (A0C (m + 1))
            (ChainSetup.step (Submission.L10.cAdopted (m + 1))) (K m)
            (DriftStopped6c.c3Adopted'' (m + 1)))ᶜ ≤ pcnt) ∧
        GoodPathBounds.logDetLow (m + 1) (DriftStopped6c.c3Adopted'' (m + 1))
          < C' - 4 * Real.log ((m + 1 : ℕ) : ℝ) ∧
        (driftRHS_acc (m + 1) (A0C (m + 1)) (DriftStopped6c.c3Adopted'' (m + 1))
              (EaccAt (m + 1) (DriftStopped6c.c3Adopted'' (m + 1))) S
            - GoodPathBounds.logDetLow (m + 1) (DriftStopped6c.c3Adopted'' (m + 1)))
            / ((C' - 4 * Real.log ((m + 1 : ℕ) : ℝ))
              - GoodPathBounds.logDetLow (m + 1) (DriftStopped6c.c3Adopted'' (m + 1)))
          + GoodPathBounds.failTotal (m + 1) pcnt < 1) :
    StateSupplyAdoptedR3 A B c3clamp C' := by
  intro m hm p hp hp0 α hα hn hraw hnd _hcov g hg _hfree _hlight
  have hm1 : 2073600 ≤ m + 1 := by
    have h2 : 2073600 ≤ m := by simpa [Threshold2.n₁] using hm
    omega
  have hN : 1 ≤ ParamsAdopted2.numStepsAdopted2 (m + 1) := by
    have := hK m; omega
  obtain ⟨S, pcnt, hS, hcnt, hLb, hbudget⟩ := hline m hm p α hα g
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
  exact stateTriple_of_cut_acc (q := qC α) (W := DriftStopped8R5.windowOfR2 α p m g)
    (A₀ := A0C (m + 1)) (r := 1) (K := K m) (ε := EaccAt (m + 1) _) (E := EaccAt (m + 1) _)
    hm1 one_pos (hK m) hc₃0 hc₃η
    (kSet_A0C_win hα hn) (hq_win hα hn) (hne_win hα hn) (StateSupply.symMat_A0C (m + 1))
    hεnn
    (ChainErrBudget.stoppedErrBudget_of_params (xs := xOf α)
      (W := DriftStopped8R5.windowOfR2 α p m g) (A₀ := A0C (m + 1))
      (ξ := ChainSetup.step (Submission.L10.cAdopted (m + 1))) hN
      (kSet_A0C_win hα hn) (StateSupply.symMat_A0C (m + 1))
      (DriftStopped7.etaAdopted_nonneg (n := m + 1))
      (DriftStopped7.r0Adopted_nonneg (n := m + 1)) hc₃0 hlt hδ1)
    (fun ω J hJ => sum_chainErr_le_c3 (xs := xOf α)
      (W := DriftStopped8R5.windowOfR2 α p m g) (A₀ := A0C (m + 1))
      (ξ := ChainSetup.step (Submission.L10.cAdopted (m + 1)))
      (kSet_A0C_win hα hn) (StateSupply.symMat_A0C (m + 1))
      (DriftStopped7.etaAdopted_nonneg (n := m + 1))
      (DriftStopped7.r0Adopted_nonneg (n := m + 1)) hc₃0 hlt hδ1 hJ)
    hS hcnt hLb hbudget

/-- **The challenge statement**, from the per-line bundle alone. -/
theorem klartag_packing_final {A B : ℝ} (hA : 0 < A) (hB : 0 ≤ B) {C' : ℝ} {K : ℕ → ℕ}
    (hK : ∀ m, K m < ParamsAdopted2.numStepsAdopted2 (m + 1))
    (hline : ∀ m : ℕ, Threshold2.n₁ ≤ m → ∀ (p : ℕ) (α : ℝ), 0 < α →
      ∀ g : Fin (m + 1) → ZMod p,
      ∃ S pcnt : ℝ,
        (S ≤ ∑ k ∈ Finset.range (K m), ∫ ω,
          DriftStopped6.stoppedFreeDim (qC α) (DriftStopped8R5.windowOfR2 α p m g) (A0C (m + 1))
            (ChainSetup.step (Submission.L10.cAdopted (m + 1)))
            (DriftStopped6.etaAdopted (m + 1)) (DriftStopped6.r0Adopted (m + 1))
            (DriftStopped6c.c3Adopted'' (m + 1)) (ParamsAdopted2.numStepsAdopted2 (m + 1)) k ω
          ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT (m + 1))))) ∧
        ((ChainSetup.gaussPath (EuclideanSpace ℝ (UT (m + 1)))).real
          (StateInvariant4.countGood (qC α) (DriftStopped8R5.windowOfR2 α p m g) (A0C (m + 1))
            (ChainSetup.step (Submission.L10.cAdopted (m + 1))) (K m)
            (DriftStopped6c.c3Adopted'' (m + 1)))ᶜ ≤ pcnt) ∧
        GoodPathBounds.logDetLow (m + 1) (DriftStopped6c.c3Adopted'' (m + 1))
          < C' - 4 * Real.log ((m + 1 : ℕ) : ℝ) ∧
        (driftRHS_acc (m + 1) (A0C (m + 1)) (DriftStopped6c.c3Adopted'' (m + 1))
              (EaccAt (m + 1) (DriftStopped6c.c3Adopted'' (m + 1))) S
            - GoodPathBounds.logDetLow (m + 1) (DriftStopped6c.c3Adopted'' (m + 1)))
            / ((C' - 4 * Real.log ((m + 1 : ℕ) : ℝ))
              - GoodPathBounds.logDetLow (m + 1) (DriftStopped6c.c3Adopted'' (m + 1)))
          + GoodPathBounds.failTotal (m + 1) pcnt < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      let V := EuclideanSpace ℝ (Fin (n + 1))
      ∃ φ : V →ₗ[ℝ] V, let E := φ '' Metric.ball (0 : V) 1
        (MeasureTheory.volume E : EReal) = c * n ^ 2 ∧
        {v ∈ E | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} :=
  StateSupplyBypass.klartag_packing_of_stateSupplyR3 hA hB
    (stateSupplyR3_of_cut_acc hK hline)

end Supply

end Submission.L10.CutAccumulated

import Submission.L10.Theorem2R3
import Submission.L10.GoodPathLight

/-!
# Gate L-10 — the light-line hand-off at the generic reach window and the repaired threshold

Brief 85c.  **`GoodPathBounds.GoodPathAt` cannot be reused here, and the reason is structural.**
`GoodPathAt` runs its chain on `DriftStopped8R.windowOfR` (`GoodPathBounds.lean:787`), i.e. over
`RawDataInst2R.shellR` at `windowR`.  `StateSupplyAdoptedR2` needs a state in
`Chain.kSet (qC α) (windowOfR2 α p m g)`, and `Chain.kSet` is **antitone** in the window
(`W' ⊆ W → kSet q W ⊆ kSet q W'`, checked).  Since `windowR ≤ windowR2` gives
`windowOfR ⊆ windowOfR2`, a `windowOfR`-path yields a state in the *larger* `kSet`, which is the
wrong direction: `kSet (windowOfR2) ⊆ kSet (windowOfR)`, not the reverse.

So `GoodPathAt2` below is `GoodPathAt` with the chain's window moved to `windowOfR2`.
`GoodPathBounds` is reported and frozen, so this is a new definition, and brief 86's discharge
(`goodPathAt_of_S`) has to be re-run at `windowOfR2` — it is the same proof, since every ingredient
is generic in the window, but it is **not** a free re-use.  That is the one thing this brief's plan
did not account for.

Everything else is a re-run: `stateTriple_of_goodPathAt` is `StateSupply.stateTriple_of_goodPath`
at `mAt` (`StateInvariant4.stateBounds_wired'` already returns `a₀ − (r₀ + c₃η)` generically, which
is `GoodPathBounds.mAt` by definition) and at the `RW2` data.
-/

set_option linter.unusedSectionVars false

namespace Submission.L10.GoodPathLightR2

open MeasureTheory Matrix Finset Module Submission.L10 Submission.L10.Increments
open Submission.L10.ConstructionA Submission.L10.Tiling Submission.L10.RawDataInst2
open Submission.L10.WindowR2 Submission.L10.GoodPathBounds
open Submission.L10.DriftStopped8R5 Submission.L10.Theorem2R3
open Submission.L10.StateSupply
open scoped ENNReal RealInnerProductSpace

variable {p m : ℕ} {α R C' : ℝ} {g : Fin (m + 1) → ZMod p}

/-! ## 1. The three window facts, at `windowOfR2` -/

theorem kSet_A0C2
    (hraw : PaddedLawSetupRW2.RawDataR p (m + 1) α R (qC α)
      (RawDataInst2RW2.shellR α (m + 1)) (A0C (m + 1))) :
    A0C (m + 1) ∈ Chain.kSet (qC α) (windowOfR2 α p m g) :=
  fun y hy => le_of_lt (hraw.hA₀ y (windowOfR2_subset hy))

theorem hq_of_raw2
    (hraw : PaddedLawSetupRW2.RawDataR p (m + 1) α R (qC α)
      (RawDataInst2RW2.shellR α (m + 1)) (A0C (m + 1))) :
    ∀ i ∈ windowOfR2 α p m g, ∀ j ∈ windowOfR2 α p m g, (0 : ℝ) ≤ ⟪qC α i, qC α j⟫ :=
  fun i hi _ _ => hraw.hq _ i (windowOfR2_subset hi)

theorem hne_of_raw2
    (hraw : PaddedLawSetupRW2.RawDataR p (m + 1) α R (qC α)
      (RawDataInst2RW2.shellR α (m + 1)) (A0C (m + 1))) :
    ∀ i ∈ windowOfR2 α p m g, qC α i ≠ 0 := by
  intro y hy
  have hr := hraw.hr y (windowOfR2_subset hy)
  have hnorm : ‖qC α y‖ = (α * ‖toE (m + 1) y‖) ^ 2 := norm_qC α y
  intro hzero
  rw [hzero, norm_zero] at hnorm
  nlinarith [hr, hnorm]

/-! ## 2. `GoodPathAt` at `windowOfR2` -/

/-- **`GoodPathBounds.GoodPathAt` with the chain's window at the generic reach.** -/
def GoodPathAt2 (p m : ℕ) (α : ℝ) (g : Fin (m + 1) → ZMod p) (c₃ C' : ℝ) : Prop :=
  ∃ (r thr : ℝ)
    (Wacc : (ℕ → EuclideanSpace ℝ (UT (m + 1))) → EuclideanSpace ℝ (UT (m + 1)))
    (K : ℕ) (ω : ℕ → EuclideanSpace ℝ (UT (m + 1))),
    K < ParamsAdopted2.numStepsAdopted2 (m + 1) ∧
    ω ∈ StateInvariant4.wiredGood' r Wacc
        (ChainSetup.step (Submission.L10.cAdopted (m + 1))) thr
        (ParamsAdopted2.numStepsAdopted2 (m + 1)) (DriftStopped6.etaAdopted (m + 1))
        (qC α) (windowOfR2 α p m g) (A0C (m + 1))
        (DriftStopped6.r0Adopted (m + 1)) c₃ ∧
    ChainWiring.logDet (Chain.chain (qC α) (windowOfR2 α p m g) (A0C (m + 1))
        (ChainSetup.step (Submission.L10.cAdopted (m + 1))) K ω).1
      ≤ C' - 4 * Real.log ((m + 1 : ℕ) : ℝ)

/-- **The state triple from a good path**, at `mAt` and `windowOfR2`. -/
theorem stateTriple_of_goodPathAt2 {c₃ : ℝ} (hm : Threshold2.n₁ ≤ m)
    (hc₃0 : 0 ≤ c₃) (hc₃ : c₃ * DriftStopped6.etaAdopted (m + 1) ≤ 1 / 4)
    (hraw : PaddedLawSetupRW2.RawDataR p (m + 1) α R (qC α)
      (RawDataInst2RW2.shellR α (m + 1)) (A0C (m + 1)))
    (hpath : GoodPathAt2 p m α g c₃ C') :
    ∃ (A : EuclideanSpace ℝ (UT (m + 1))) (M : ℝ),
      A ∈ Chain.kSet (qC α) (windowOfR2 α p m g) ∧
      Discharge.StateBounds (symMat A) (mAt (m + 1) c₃) M ∧
      ChainWiring.logDet A ≤ C' - 4 * Real.log ((m + 1 : ℕ) : ℝ) := by
  obtain ⟨r, thr, Wacc, K, ω, hK, hω, hlog⟩ := hpath
  have hm1 : 2073600 ≤ m + 1 := by
    have h2 : 2073600 ≤ m := by simpa [Threshold2.n₁] using hm
    omega
  have hA₀ : A0C (m + 1) ∈ Chain.kSet (qC α) (windowOfR2 α p m g) := kSet_A0C2 hraw
  have hq := hq_of_raw2 (g := g) hraw
  have hne := hne_of_raw2 (g := g) hraw
  have hlt : DriftStopped6.r0Adopted (m + 1) + c₃ * DriftStopped6.etaAdopted (m + 1)
      < a0C (m + 1) := by
    have h := half_le_mAt hm1 hc₃
    rw [mAt] at h
    linarith
  refine ⟨(Chain.chain (qC α) (windowOfR2 α p m g) (A0C (m + 1))
      (ChainSetup.step (Submission.L10.cAdopted (m + 1))) K ω).1,
    MAt (m + 1) c₃, Chain.chain_fst_mem_kSet hA₀ hq hne K ω, ?_, hlog⟩
  exact StateInvariant4.stateBounds_wired' hA₀ hq hne (symMat_A0C (m + 1))
    (DriftStopped7.etaAdopted_nonneg (n := m + 1))
    (DriftStopped7.r0Adopted_nonneg (n := m + 1)) hc₃0 hlt K hK ω hω

/-! ## 3. The light-line hand-off -/

/-- **The statement the discharge must produce**, at the generic reach window and the repaired
contact threshold. -/
def LightGoodPath2 (c₃ : ℕ → ℝ) (w : ∀ _p m : ℕ, ℝ → (Fin (m + 1) → ℤ) → ℝ≥0∞)
    (θ : ℕ → ℕ → ℝ → ℝ≥0∞) (C' : ℝ) : Prop :=
  ∀ m : ℕ, Threshold2.n₁ ≤ m → ∀ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p) (α : ℝ),
    0 < α → ∀ g : Fin (m + 1) → ZMod p, g ≠ 0 →
      (∀ y : Fin (m + 1) → ℤ, y ≠ 0 →
        ‖toE (m + 1) y‖ ≤ (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α → y ∉ latZ p (m + 1) g) →
      Theorem2.LightContact (w p m α) (RawDataInst2RW2.shellR α (m + 1)) (θ p m α) g →
      GoodPathAt2 p m α g (c₃ (m + 1)) C'

/-- **`StateSupplyAdoptedR2` from the light-line form** — report 82a's named hand-off, re-run at
`mAt` and `windowOfR2`. -/
theorem stateSupplyAdoptedR2_of_goodPathAt {c₃ : ℕ → ℝ} (hc₃0 : ∀ n, 0 ≤ c₃ n)
    (hc₃ : ∀ n, c₃ n * DriftStopped6.etaAdopted n ≤ 1 / 4)
    {w : ∀ _p m : ℕ, ℝ → (Fin (m + 1) → ℤ) → ℝ≥0∞} {θ : ℕ → ℕ → ℝ → ℝ≥0∞} {C' : ℝ}
    (hgood : LightGoodPath2 c₃ w θ C') : StateSupplyAdoptedR2 c₃ w θ C' := by
  intro m hm p hp hp0 α hα hn hraw hnd _hcov g hg hfree hlight
  exact stateTriple_of_goodPathAt2 hm (hc₃0 (m + 1)) (hc₃ (m + 1)) hraw
    (hgood m hm p hp hp0 α hα g hg hfree hlight)

/-- **The gate from the light-line hypothesis**, at the generic reach window and the repaired
threshold. -/
theorem klartag_packing_of_lightGoodPath2 {c₃ : ℕ → ℝ} (hc₃0 : ∀ n, 0 ≤ c₃ n)
    (hc₃ : ∀ n, c₃ n * DriftStopped6.etaAdopted n ≤ 1 / 4)
    {θ : ℕ → ℕ → ℝ → ℝ≥0∞} {C' : ℝ}
    (hpr : ParamsProducerR2 θ) (h : LightGoodPath2 c₃ wR2 θ C') :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      let V := EuclideanSpace ℝ (Fin (n + 1))
      ∃ φ : V →ₗ[ℝ] V, let E := φ '' Metric.ball (0 : V) 1
        (MeasureTheory.volume E : EReal) = c * n ^ 2 ∧
        {v ∈ E | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} :=
  klartag_packing_of_stateSupplyR2 hc₃0 hc₃ hpr
    (stateSupplyAdoptedR2_of_goodPathAt hc₃0 hc₃ h)

end Submission.L10.GoodPathLightR2

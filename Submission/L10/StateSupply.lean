import Submission.L10.DriftConstant
import Submission.L10.DriftStopped8R
import Submission.L10.DriftInputsStopped
import Submission.L10.LatticeDataR
import Submission.L10.Theorem2R

/-!
# Gate L-10 (`klartag_packing`) — the state supply at the reach window

Brief 76.  `DriftStopped8R.StateSupplyAdoptedR w θ C'` (`:149`) asks, for each dimension above the
threshold and each good line, for a chain state `A` on the drift's own window `W_g` that is in
`K_L`, obeys `StateBounds` at the adopted lower bound, and satisfies eq. (68)'s log-determinant
bound.  `C' := 2·10⁵` (report 80: `C'` runs `1.8035·10⁵ → 1.949·10⁵`, so `2·10⁵` serves every
`n ≥ n₁`, and `c₀ = exp(−10⁵) > 0`).

## What this module does

Everything downstream of **one** residual: a path of `StateInvariant4.wiredGood'` carrying the
log-determinant bound.  Given that path, all three conjuncts follow with no further probability:

* `A ∈ Chain.kSet (qC α) (windowOfR α p m g)` — `Chain.chain_fst_mem_kSet`, which holds at every
  step and on every path, from `RawDataR`'s own fields restricted to `W_g`
  (`LatticeDataR.rawData_monoR`);
* `StateBounds (symMat A) (mAdopted (m+1)) M` — `StateInvariant4.stateBounds_wired'` on the good
  event, at `M = MAdopted (m+1)`; the two bounds are `a₀ ∓ (r₀ + c₃η)` **definitionally**;
* the log-determinant bound — the path's own.

The residual is `GoodPath`, and report 80 §1 is how it is produced: `drift_bound_stopped_adopted`
(brief 75) gives the terminal bound in expectation, `DriftConstant.kappa_mul_S_ge` and
`logDet_target_of_drift` turn the contact total into the constant, and
`DriftStopped6.exists_le_of_integral_le` with `exists_mem_inter_of_one_lt` and
`exists_logDet_le_on_wiredGood'` land it on the good event.  What is *not* discharged here is named
in the report: the free-dimension total `S` from the light contact, and the three failure bounds.

`DriftStopped8R.lean`, `DriftInputsStopped.lean` and `LatticeDataR.lean` are reported and are not
edited; this module imports them.
-/

set_option linter.unusedSectionVars false

namespace Submission.L10.StateSupply

open MeasureTheory Matrix Finset Module Submission.L10 Submission.L10.Increments
open Submission.L10.ConstructionA Submission.L10.Tiling
open Submission.L10.PaddedLawSetupR Submission.L10.RawDataInst2R Submission.L10.RawDataInst2
open Submission.L10.TailSideSetup2 Submission.L10.DriftStopped8R
open scoped ENNReal RealInnerProductSpace

/-! ## 1. The chain data on `W_g`, from `RawDataR` -/

section Data

variable {p m : ℕ} {α R : ℝ} {g : Fin (m + 1) → ZMod p}

theorem windowOfR_subset : windowOfR α p m g ⊆ shellR α (m + 1) :=
  fun _ hy => (mem_windowOfR.1 hy).1

/-- `A₀ ∈ K_L` on the drift's window: `RawDataR.hA₀` is the strict form. -/
theorem kSet_A0C (hraw : RawDataR p (m + 1) α R (qC α) (shellR α (m + 1)) (A0C (m + 1))) :
    A0C (m + 1) ∈ Chain.kSet (qC α) (windowOfR α p m g) :=
  fun y hy => le_of_lt (hraw.hA₀ y (windowOfR_subset hy))

theorem hq_of_raw (hraw : RawDataR p (m + 1) α R (qC α) (shellR α (m + 1)) (A0C (m + 1))) :
    ∀ i ∈ windowOfR α p m g, ∀ j ∈ windowOfR α p m g, (0 : ℝ) ≤ ⟪qC α i, qC α j⟫ :=
  fun i hi _ _ => hraw.hq _ i (windowOfR_subset hi)

/-- `q y ≠ 0` on the window: `‖qC α y‖ = (α‖toE y‖)²` and `RawDataR.hr` makes that positive. -/
theorem hne_of_raw (hraw : RawDataR p (m + 1) α R (qC α) (shellR α (m + 1)) (A0C (m + 1))) :
    ∀ i ∈ windowOfR α p m g, qC α i ≠ 0 := by
  intro y hy
  have hr := hraw.hr y (windowOfR_subset hy)
  have hnorm : ‖qC α y‖ = (α * ‖toE (m + 1) y‖) ^ 2 := norm_qC α y
  intro hzero
  rw [hzero, norm_zero] at hnorm
  nlinarith [hr, hnorm]

/-- `symMat A₀ = a₀ • 1`, from `A0C = a₀ • idUT` and `symMat_idUT`. -/
theorem symMat_A0C (n : ℕ) :
    symMat (A0C n) = a0C n • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  rw [A0C, StateInvariant.symMat_smul, symMat_idUT]

end Data

/-! ## 2. The residual: a good path carrying the eq. (68) bound -/

/-- **The one probabilistic residual.**  A path of `wiredGood'` on the drift's own window whose
chain log-determinant at some index below the horizon meets eq. (68).  Report 80 §1 is the route
that produces it; §3 of the report names what is still owed on that route. -/
def GoodPath (p m : ℕ) (α : ℝ) (g : Fin (m + 1) → ZMod p) (C' : ℝ) : Prop :=
  ∃ (r thr : ℝ)
    (Wacc : (ℕ → EuclideanSpace ℝ (UT (m + 1))) → EuclideanSpace ℝ (UT (m + 1)))
    (K : ℕ) (ω : ℕ → EuclideanSpace ℝ (UT (m + 1))),
    K < ParamsAdopted2.numStepsAdopted2 (m + 1) ∧
    ω ∈ StateInvariant4.wiredGood' r Wacc
        (ChainSetup.step (Submission.L10.cAdopted (m + 1))) thr
        (ParamsAdopted2.numStepsAdopted2 (m + 1)) (DriftStopped6.etaAdopted (m + 1))
        (qC α) (windowOfR α p m g) (A0C (m + 1))
        (DriftStopped6.r0Adopted (m + 1)) (DriftStopped6.c3Adopted (m + 1)) ∧
    ChainWiring.logDet (Chain.chain (qC α) (windowOfR α p m g) (A0C (m + 1))
        (ChainSetup.step (Submission.L10.cAdopted (m + 1))) K ω).1
      ≤ C' - 4 * Real.log ((m + 1 : ℕ) : ℝ)

/-! ## 3. The assembly -/

section Assembly

/-- **The three conjuncts from one good path.**  No probability is used here: `K_L` membership is
structural, the state bounds are the good event's, and the log-determinant bound is the path's. -/
theorem stateTriple_of_goodPath {p m : ℕ} {α R C' : ℝ} {g : Fin (m + 1) → ZMod p}
    (hm : Threshold2.n₁ ≤ m)
    (hraw : RawDataR p (m + 1) α R (qC α) (shellR α (m + 1)) (A0C (m + 1)))
    (hpath : GoodPath p m α g C') :
    ∃ (A : EuclideanSpace ℝ (UT (m + 1))) (M : ℝ),
      A ∈ Chain.kSet (qC α) (windowOfR α p m g) ∧
      Discharge.StateBounds (symMat A) (DriftStopped6.mAdopted (m + 1)) M ∧
      ChainWiring.logDet A ≤ C' - 4 * Real.log ((m + 1 : ℕ) : ℝ) := by
  obtain ⟨r, thr, Wacc, K, ω, hK, hω, hlog⟩ := hpath
  have hm1 : 2073600 ≤ m + 1 := by
    have h2 : 2073600 ≤ m := by simpa [Threshold2.n₁] using hm
    omega
  have hA₀ : A0C (m + 1) ∈ Chain.kSet (qC α) (windowOfR α p m g) := kSet_A0C hraw
  have hq := hq_of_raw (g := g) hraw
  have hne := hne_of_raw (g := g) hraw
  have hlt : DriftStopped6.r0Adopted (m + 1)
      + DriftStopped6.c3Adopted (m + 1) * DriftStopped6.etaAdopted (m + 1) < a0C (m + 1) := by
    have h := DriftStopped7.half_le_mAdopted hm1
    rw [DriftStopped6.mAdopted] at h
    linarith
  refine ⟨(Chain.chain (qC α) (windowOfR α p m g) (A0C (m + 1))
      (ChainSetup.step (Submission.L10.cAdopted (m + 1))) K ω).1,
    DriftStopped6.MAdopted (m + 1),
    Chain.chain_fst_mem_kSet hA₀ hq hne K ω, ?_, hlog⟩
  exact StateInvariant4.stateBounds_wired' hA₀ hq hne (symMat_A0C (m + 1))
    (DriftStopped7.etaAdopted_nonneg (n := m + 1))
    (DriftStopped7.r0Adopted_nonneg (n := m + 1))
    (by rw [DriftStopped6.c3Adopted]; positivity) hlt K hK ω hω

/-- **`StateSupplyAdoptedR` at `C' = 2·10⁵`**, from the good path at every dimension and line.
The weight and threshold families are untouched: the residual does not read them, so the
specialisation to brief 81's families is definitional. -/
theorem stateSupplyAdoptedR_of_goodPath
    {w : ∀ m : ℕ, ℝ → (Fin (m + 1) → ℤ) → ℝ≥0∞} {θ : ℕ → ℝ → ℝ≥0∞} {C' : ℝ}
    (hgood : ∀ m : ℕ, Threshold2.n₁ ≤ m → ∀ (p : ℕ) (α : ℝ), 0 < α →
      ∀ g : Fin (m + 1) → ZMod p, g ≠ 0 → GoodPath p m α g C') :
    DriftStopped8R.StateSupplyAdoptedR w θ C' := by
  intro m hm p hp hp0 α hα hn hraw hnd _hcov g hg _hfree _hlight
  exact stateTriple_of_goodPath hm hraw (hgood m hm p α hα g hg)

/-- **The drift side, and so the gate, from the good path alone.** -/
theorem driftSideW_of_goodPath
    {w : ∀ m : ℕ, ℝ → (Fin (m + 1) → ℤ) → ℝ≥0∞} {θ : ℕ → ℝ → ℝ≥0∞}
    (hgood : ∀ m : ℕ, Threshold2.n₁ ≤ m → ∀ (p : ℕ) (α : ℝ), 0 < α →
      ∀ g : Fin (m + 1) → ZMod p, g ≠ 0 → GoodPath p m α g 200000) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ DriftStopped8R.DriftSideW w θ c₀ :=
  DriftStopped8R.driftSide''''_of_stateSupplyR (stateSupplyAdoptedR_of_goodPath hgood)

/-- **The gate, on two hypotheses.**  `ParamsProducerR` is brief 81's fold-in; `GoodPath` is the
probabilistic residual of §2.  Nothing else is assumed: the band is discharged
(`DriftStopped8R.bandSideAdoptedR`), the tail side is `LatticeDataR.rawData_exists'R`, the drift
record is `DriftInputsStopped.driftInputs_stopped_adopted`, the maximal lane is `GaussianMaximal3`,
and `c₀ = exp(−10⁵)` is produced. -/
theorem klartag_packing_final
    {w : ∀ m : ℕ, ℝ → (Fin (m + 1) → ℤ) → ℝ≥0∞} {θ : ℕ → ℝ → ℝ≥0∞}
    (hpr : Theorem2R.ParamsProducerR w θ)
    (hgood : ∀ m : ℕ, Threshold2.n₁ ≤ m → ∀ (p : ℕ) (α : ℝ), 0 < α →
      ∀ g : Fin (m + 1) → ZMod p, g ≠ 0 → GoodPath p m α g 200000) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      let V := EuclideanSpace ℝ (Fin (n + 1))
      ∃ φ : V →ₗ[ℝ] V, let E := φ '' Metric.ball (0 : V) 1
        (MeasureTheory.volume E : EReal) = c * n ^ 2 ∧
        {v ∈ E | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} :=
  Theorem2R.klartag_packing_of_stateSupplyR hpr (stateSupplyAdoptedR_of_goodPath hgood)

end Assembly

end Submission.L10.StateSupply

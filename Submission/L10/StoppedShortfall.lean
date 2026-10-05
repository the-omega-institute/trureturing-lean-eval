/-
Gate L-10 (`klartag_packing`), brief 96b — the pathwise lower bound in the shape
`ShortfallBound.shortfall_le` binds: `X ≥ c + M − D` with `c = logDet A₀`, `M = mgPart … K` the
deterministic martingale of `LogDetMartingale`, and `D` measurable with a deterministic range.

The two random-range sums of `StoppedLowerBound.logDet_stopped_ge` are both dominated here:

* the martingale sum by `MidTerm.sum_Vcoef_ge`, `∑_{j<K'} ⟪V_j, ξ_j⟫ ≥ mgPart … K − midCap`;
* the Frobenius sum by `∑_{j<K'} ‖H_j‖² ≤ (1+ε)·∑_{j<K} min(‖ξ_j‖², η²) + (1+1/ε)·(c₃η)²`,
  using `‖π_jξ_j‖ ≤ ‖ξ_j‖ ≤ η` below `τ` and `∑_j ‖liftStep_j‖ ≤ c₃η` for the whole lift.

The lift's contribution is a **square of a sum**, not a sum of squares: `∑ ‖ℓ_j‖² ≤ (∑ ‖ℓ_j‖)²`,
and `∑ ‖ℓ_j‖ ≤ card(C_K)·η ≤ c₃η`.  Charging it per step instead would cost `K·(c₃η)²`, which is
`16 n⁷ log n / √n` — the whole budget many times over.

Nothing reported is edited.
-/
import Submission.L10.MidTerm
import Submission.L10.StepTruncVariance

set_option linter.unusedSectionVars false

namespace Submission.L10.StoppedShortfall

open MeasureTheory Matrix Finset Module
open scoped RealInnerProductSpace
open Submission.L10 Submission.L10.Increments Submission.L10.StoppedChain
open Submission.L10.DriftStopped Submission.L10.LogDetMartingale

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι] {Ω : Type*} [MeasurableSpace Ω]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

/-! ## 1. The lift, summed as a square of a sum -/

/-- `∑_{j<K} ‖ℓ_j‖ ≤ card(C_K)·η`, the intermediate step of `LiftBound.norm_liftSum_le_card`. -/
theorem sum_norm_liftStep_le {η : ℝ} {K : ℕ} {ω : Ω}
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hstep : ∀ j, j < K → ‖StateInvariant.gaussStep q W A₀ ξ j ω‖ ≤ η) :
    ∑ j ∈ Finset.range K, ‖StateInvariant.liftStep q W A₀ ξ j ω‖
      ≤ ((Chain.chain q W A₀ ξ K ω).2.card : ℝ) * η := by
  classical
  calc ∑ j ∈ Finset.range K, ‖StateInvariant.liftStep q W A₀ ξ j ω‖
      ≤ ∑ j ∈ Finset.range K, ((Chain.newActive q W A₀ ξ j ω).card : ℝ) * η :=
        Finset.sum_le_sum fun j hj =>
          le_trans (StateInvariant2.norm_liftStep_le hA₀ hq hne j ω)
            (mul_le_mul_of_nonneg_left (hstep j (Finset.mem_range.1 hj)) (Nat.cast_nonneg _))
    _ = (∑ j ∈ Finset.range K, ((Chain.newActive q W A₀ ξ j ω).card : ℝ)) * η := by
        rw [Finset.sum_mul]
    _ = ((Chain.chain q W A₀ ξ K ω).2.card : ℝ) * η := by
        rw [← Nat.cast_sum, LiftBound.sum_card_newActive hA₀ hq hne K ω]

/-- A sum of squares of non-negatives is at most the square of the sum. -/
theorem sum_sq_le_sq_sum {K : ℕ} (f : ℕ → ℝ) (hf : ∀ j, 0 ≤ f j) :
    ∑ j ∈ Finset.range K, (f j) ^ 2 ≤ (∑ j ∈ Finset.range K, f j) ^ 2 := by
  classical
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have h0 : (0 : ℝ) ≤ ∑ j ∈ Finset.range K, f j :=
      Finset.sum_nonneg fun j _ => hf j
    nlinarith [ih, h0, hf K]

/-- **`∑_{j<K} ‖ℓ_j‖² ≤ (c₃η)²`** on a path whose count stays below `c₃`. -/
theorem sum_liftStep_sq_le {η c₃ : ℝ} {K : ℕ} {ω : Ω} (hη : 0 ≤ η)
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hstep : ∀ j, j < K → ‖StateInvariant.gaussStep q W A₀ ξ j ω‖ ≤ η)
    (hcard : ((Chain.chain q W A₀ ξ K ω).2.card : ℝ) ≤ c₃) :
    ∑ j ∈ Finset.range K, ‖StateInvariant.liftStep q W A₀ ξ j ω‖ ^ 2 ≤ (c₃ * η) ^ 2 := by
  have h1 := sum_sq_le_sq_sum (K := K)
    (fun j => ‖StateInvariant.liftStep q W A₀ ξ j ω‖) (fun j => norm_nonneg _)
  have h2 := sum_norm_liftStep_le hA₀ hq hne hstep
  have h3 : ((Chain.chain q W A₀ ξ K ω).2.card : ℝ) * η ≤ c₃ * η :=
    mul_le_mul_of_nonneg_right hcard hη
  have h0 : (0 : ℝ) ≤ ∑ j ∈ Finset.range K, ‖StateInvariant.liftStep q W A₀ ξ j ω‖ :=
    Finset.sum_nonneg fun j _ => norm_nonneg _
  nlinarith [h1, h2, h3, h0]

/-! ## 2. The Gaussian half, against the truncated step -/

/-- **`‖π_jξ_j‖² ≤ min(‖ξ_j‖², η²)`** whenever the raw step is capped by `η`. -/
theorem norm_gaussStep_sq_le_trunc {η : ℝ} {c : ℝ} {j : ℕ}
    {ω : ℕ → EuclideanSpace ℝ (UT n)} {W' : Finset ι} {A₀' : EuclideanSpace ℝ (UT n)}
    (hξ : ‖ChainSetup.step c j ω‖ ≤ η) :
    ‖StateInvariant.gaussStep q W' A₀' (ChainSetup.step c) j ω‖ ^ 2
      ≤ StepTruncVariance.sqTrunc c (η ^ 2) j ω := by
  have hle : ‖StateInvariant.gaussStep q W' A₀' (ChainSetup.step c) j ω‖
      ≤ ‖ChainSetup.step c j ω‖ := Submodule.norm_starProjection_apply_le _ _
  have h0 : (0 : ℝ) ≤ ‖StateInvariant.gaussStep q W' A₀' (ChainSetup.step c) j ω‖ :=
    norm_nonneg _
  refine le_min ?_ ?_
  · exact pow_le_pow_left₀ h0 hle 2
  · exact pow_le_pow_left₀ h0 (le_trans hle hξ) 2


/-! ## 3. The assembly: `X ≥ c + M − D` with `D` measurable on a deterministic range -/

section Assembly

variable {xs : ι → (Fin n → ℝ)}

/-- **The pathwise lower bound `ShortfallBound.shortfall_le` consumes.**  `M` is
`LogDetMartingale.mgPart … K`, whose second moment is `variance_M_le`; `D` is a non-negative
multiple of the truncated chi-square sum, a constant, and `MidTerm.midCap`, all three measurable
with deterministic ranges. -/
theorem logDet_stopped_ge_final {η a₀ r₀ c₃ rr ε cstep : ℝ} {N K : ℕ}
    {ω : ℕ → EuclideanSpace ℝ (UT n)}
    (hA₀ : A₀ ∈ Chain.kSet (fun i => ChainWiring.qUT (xs i)) W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪ChainWiring.qUT (xs i), ChainWiring.qUT (xs j)⟫)
    (hne : ∀ i ∈ W, ChainWiring.qUT (xs i) ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hN : 1 ≤ N) (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃) (hlt : r₀ + c₃ * η < a₀)
    (hrr0 : 0 ≤ rr) (hrr : rr ≤ 1 / 2)
    (hrm : (1 + c₃) * η ≤ rr * (a₀ - (r₀ + c₃ * η))) (hε : 0 < ε) :
    ChainWiring.logDet A₀
        + mgPart (fun i => ChainWiring.qUT (xs i)) W A₀ (ChainSetup.step cstep) η r₀ c₃ N K ω
        - (((1 / 2 + 2 * rr) / (a₀ - (r₀ + c₃ * η)) ^ 2)
              * ((1 + ε) * (∑ j ∈ Finset.range K, StepTruncVariance.sqTrunc cstep (η ^ 2) j ω)
                  + (1 + 1 / ε) * (c₃ * η) ^ 2)
            + MidTerm.midCap (fun i => ChainWiring.qUT (xs i)) W A₀
                (ChainSetup.step cstep) η r₀ c₃ N K ω)
      ≤ stoppedLogDet (fun i => ChainWiring.qUT (xs i)) W A₀
          (ChainSetup.step cstep) η r₀ c₃ N K ω := by
  classical
  set Q := fun i => ChainWiring.qUT (xs i) with hQ
  set ξ := ChainSetup.step (ι := UT n) cstep with hξdef
  set τ := tau Q W A₀ ξ η r₀ c₃ N ω with hτ
  set K' := min K (τ - 1) with hK'
  set κ := (1 / 2 + 2 * rr) / (a₀ - (r₀ + c₃ * η)) ^ 2 with hκ
  have hm : (0 : ℝ) < a₀ - (r₀ + c₃ * η) := by linarith
  have hκ0 : (0 : ℝ) ≤ κ := by rw [hκ]; positivity
  -- the telescoped bound
  have hbase := StoppedLowerBound.logDet_stopped_ge (q := Q) (W := W) (A₀ := A₀) (ξ := ξ)
    (xs := xs) (N := N) (K := K) (ω := ω) rfl hA₀ hq hne hA₀m hη hr₀ hlt hrr0 hrr hrm
  -- the state conditions at the cut index
  have hK'τ : K' < τ := by
    have h1 : 1 ≤ τ := one_le_tau (q := Q) (W := W) (A₀ := A₀) (ξ := ξ)
      (η := η) (r₀ := r₀) (c₃ := c₃) (N := N) hN hr₀ hc₃ ω
    rw [hK']; omega
  have hstate := stateGood_of_lt_tau (N := N) (q := Q) (W := W) (A₀ := A₀) (ξ := ξ)
    (η := η) (r₀ := r₀) (c₃ := c₃) hK'τ
  have hstep : ∀ j, j < K' → ‖StateInvariant.gaussStep Q W A₀ ξ j ω‖ ≤ η := fun j hj =>
    le_trans (Submodule.norm_starProjection_apply_le _ _) (hstate.1 j hj)
  -- the Frobenius sum
  have hfro : ∑ j ∈ Finset.range K', ‖LogDetChainLower.incr Q W A₀ ξ j ω‖ ^ 2
      ≤ (1 + ε) * (∑ j ∈ Finset.range K, StepTruncVariance.sqTrunc cstep (η ^ 2) j ω)
        + (1 + 1 / ε) * (c₃ * η) ^ 2 := by
    have hsplit : ∑ j ∈ Finset.range K', ‖LogDetChainLower.incr Q W A₀ ξ j ω‖ ^ 2
        ≤ ∑ j ∈ Finset.range K',
            ((1 + ε) * ‖StateInvariant.gaussStep Q W A₀ ξ j ω‖ ^ 2
              + (1 + 1 / ε) * ‖StateInvariant.liftStep Q W A₀ ξ j ω‖ ^ 2) :=
      Finset.sum_le_sum fun j _ => LogDetChainLower.norm_incr_sq_le hε j ω
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsplit
    have hg : ∑ j ∈ Finset.range K', ‖StateInvariant.gaussStep Q W A₀ ξ j ω‖ ^ 2
        ≤ ∑ j ∈ Finset.range K, StepTruncVariance.sqTrunc cstep (η ^ 2) j ω := by
      have h1 : ∑ j ∈ Finset.range K', ‖StateInvariant.gaussStep Q W A₀ ξ j ω‖ ^ 2
          ≤ ∑ j ∈ Finset.range K', StepTruncVariance.sqTrunc cstep (η ^ 2) j ω :=
        Finset.sum_le_sum fun j hj =>
          norm_gaussStep_sq_le_trunc (q := Q) (W' := W) (A₀' := A₀)
            (hstate.1 j (Finset.mem_range.1 hj))
      have hKle : K' ≤ K := by rw [hK']; exact min_le_left _ _
      have hsubset : Finset.range K' ⊆ Finset.range K := by
        intro x hx
        simp only [Finset.mem_range] at hx ⊢
        omega
      refine le_trans h1 (Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_)
      exact fun j _ _ => (StepTruncVariance.sqTrunc_mem_Icc (c := cstep) (by positivity) j ω).1
    have hl : ∑ j ∈ Finset.range K', ‖StateInvariant.liftStep Q W A₀ ξ j ω‖ ^ 2
        ≤ (c₃ * η) ^ 2 := sum_liftStep_sq_le hη hA₀ hq hne hstep hstate.2.2
    have he1 : (0 : ℝ) ≤ 1 + ε := by linarith
    have he2 : (0 : ℝ) ≤ 1 + 1 / ε := by positivity
    nlinarith [hsplit, hg, hl, he1, he2]
  -- the martingale sum
  have hmg := MidTerm.sum_Vcoef_ge (q := Q) (W := W) (A₀ := A₀) (ξ := ξ)
    (η := η) (r₀ := r₀) (c₃ := c₃) (N := N) (K := K) (ω := ω)
  have hfro' : κ * (∑ j ∈ Finset.range K', ‖LogDetChainLower.incr Q W A₀ ξ j ω‖ ^ 2)
      ≤ κ * ((1 + ε) * (∑ j ∈ Finset.range K, StepTruncVariance.sqTrunc cstep (η ^ 2) j ω)
          + (1 + 1 / ε) * (c₃ * η) ^ 2) := mul_le_mul_of_nonneg_left hfro hκ0
  rw [stoppedLogDet]
  linarith [hbase, hmg, hfro']

end Assembly

end Submission.L10.StoppedShortfall


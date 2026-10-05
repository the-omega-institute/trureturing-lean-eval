/-
Gate L-10 (`klartag_packing`), brief 96b — the single middle term, and its second moment.

`StoppedLowerBound.logDet_stopped_ge` accumulates `∑_{j < min K (τ−1)} ⟪V_j, ξ_j⟫`, because that is
the index `stoppedState` reads.  `LogDetMartingale.variance_M_le` bounds the second moment of
`mgPart … K`, the sum over the **deterministic** range `[0, K)`.  The two differ by exactly one
term — `j = τ−1`, when `τ−1 < K` — since `stoppedV` vanishes at every `j ≥ τ`.  This is the tree's
"middle case", the single step where the stopped and unstopped cuts disagree.

The term is charged to the **drift** side, not the martingale side, so `M` stays the deterministic
`mgPart … K` and `variance_M_le` applies verbatim.  Its second moment costs nothing new:
`mid² ≤ ∑_{j<K} Δ_j²` because at most one summand is non-zero, and `∑_j E[Δ_j²]` is already
bounded by `LogDetMartingale.integral_mgIncr_sq_le`.

Nothing reported is edited.
-/
import Submission.L10.LogDetMartingale
import Submission.L10.StoppedLowerBound

set_option linter.unusedSectionVars false

namespace Submission.L10.MidTerm

open MeasureTheory Matrix Finset Module
open scoped RealInnerProductSpace
open Submission.L10 Submission.L10.Increments Submission.L10.StoppedChain
open Submission.L10.DriftStopped Submission.L10.LogDetMartingale

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι] {Ω : Type*} [MeasurableSpace Ω]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

/-! ## 1. The increment vanishes past the stopping time -/

theorem stoppedV_eq_zero {η r₀ c₃ : ℝ} {N j : ℕ} {ω : Ω}
    (hj : tau q W A₀ ξ η r₀ c₃ N ω ≤ j) :
    stoppedV q W A₀ ξ η r₀ c₃ N j ω = 0 := by
  rw [stoppedV, ite_eq_right (by omega)]

theorem mgIncr_eq_zero {η r₀ c₃ : ℝ} {N j : ℕ} {ω : Ω}
    (hj : tau q W A₀ ξ η r₀ c₃ N ω ≤ j) :
    mgIncr q W A₀ ξ η r₀ c₃ N j ω = 0 := by
  rw [mgIncr, stoppedV_eq_zero hj, inner_zero_left]

/-- Below the stopping time the stopped coefficient is the chain's own. -/
theorem mgIncr_eq_inner {η r₀ c₃ : ℝ} {N j : ℕ} {ω : Ω}
    (hj : j < tau q W A₀ ξ η r₀ c₃ N ω) :
    mgIncr q W A₀ ξ η r₀ c₃ N j ω
      = ⟪LogDetChainLower.Vcoef q W A₀ ξ j ω, ξ j ω⟫ := by
  rw [mgIncr, stoppedV, ite_eq_left hj, LogDetChainLower.Vcoef]

/-! ## 2. The middle term -/

/-- **The single step the two cuts disagree on.** -/
noncomputable def mid (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι)
    (A₀ : EuclideanSpace ℝ (UT n)) (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n))
    (η r₀ c₃ : ℝ) (N K : ℕ) (ω : Ω) : ℝ :=
  mgPart q W A₀ ξ η r₀ c₃ N K ω
    - ∑ j ∈ Finset.range (min K (tau q W A₀ ξ η r₀ c₃ N ω - 1)),
        mgIncr q W A₀ ξ η r₀ c₃ N j ω

/-- **`mid` is one increment or nothing.** -/
theorem mid_eq {η r₀ c₃ : ℝ} {N K : ℕ} {ω : Ω} :
    mid q W A₀ ξ η r₀ c₃ N K ω
      = if tau q W A₀ ξ η r₀ c₃ N ω - 1 < K then
          mgIncr q W A₀ ξ η r₀ c₃ N (tau q W A₀ ξ η r₀ c₃ N ω - 1) ω else 0 := by
  classical
  set τ := tau q W A₀ ξ η r₀ c₃ N ω with hτ
  rw [mid, mgPart]
  by_cases hc : τ - 1 < K
  · rw [ite_eq_left hc, min_eq_right (by omega)]
    have hsplit : Finset.range K
        = Finset.range (τ - 1) ∪ Finset.Ico (τ - 1) K := by
      rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
        Finset.Ico_union_Ico_eq_Ico (Nat.zero_le _) (le_of_lt hc)]
    have hdisj : Disjoint (Finset.range (τ - 1)) (Finset.Ico (τ - 1) K) := by
      rw [Finset.range_eq_Ico]
      exact Finset.Ico_disjoint_Ico_consecutive 0 (τ - 1) K
    rw [hsplit, Finset.sum_union hdisj, add_sub_cancel_left]
    rw [Finset.sum_eq_sum_Ico_succ_bot hc]
    have hrest : ∑ j ∈ Finset.Ico (τ - 1 + 1) K, mgIncr q W A₀ ξ η r₀ c₃ N j ω = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [Finset.mem_Ico] at hj
      exact mgIncr_eq_zero (by omega)
    rw [hrest, add_zero]
  · rw [ite_eq_right hc, min_eq_left (by omega), sub_self]

/-- **`mid² ≤ ∑_{j<K} Δ_j²`** — at most one summand is non-zero. -/
theorem mid_sq_le {η r₀ c₃ : ℝ} {N K : ℕ} {ω : Ω} :
    (mid q W A₀ ξ η r₀ c₃ N K ω) ^ 2
      ≤ ∑ j ∈ Finset.range K, (mgIncr q W A₀ ξ η r₀ c₃ N j ω) ^ 2 := by
  classical
  rw [mid_eq]
  by_cases hc : tau q W A₀ ξ η r₀ c₃ N ω - 1 < K
  · rw [ite_eq_left hc]
    refine Finset.single_le_sum (f := fun j => (mgIncr q W A₀ ξ η r₀ c₃ N j ω) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_range.2 hc)
  · rw [ite_eq_right hc]
    have : (0 : ℝ) ^ 2 = 0 := by norm_num
    rw [this]
    exact Finset.sum_nonneg fun j _ => sq_nonneg _

/-! ## 3. The stopped accumulation, restated on `mgPart` -/

/-- **`∑_{j < min K (τ−1)} ⟪V_j, ξ_j⟫ = mgPart … K − mid`.**  The telescoped sum of
`StoppedLowerBound.logDet_stopped_ge` in terms of the martingale `LogDetMartingale` bounds. -/
theorem sum_Vcoef_eq {η r₀ c₃ : ℝ} {N K : ℕ} {ω : Ω} :
    (∑ j ∈ Finset.range (min K (tau q W A₀ ξ η r₀ c₃ N ω - 1)),
        ⟪LogDetChainLower.Vcoef q W A₀ ξ j ω, ξ j ω⟫)
      = mgPart q W A₀ ξ η r₀ c₃ N K ω - mid q W A₀ ξ η r₀ c₃ N K ω := by
  have hcongr : (∑ j ∈ Finset.range (min K (tau q W A₀ ξ η r₀ c₃ N ω - 1)),
        ⟪LogDetChainLower.Vcoef q W A₀ ξ j ω, ξ j ω⟫)
      = ∑ j ∈ Finset.range (min K (tau q W A₀ ξ η r₀ c₃ N ω - 1)),
          mgIncr q W A₀ ξ η r₀ c₃ N j ω := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjlt : j < tau q W A₀ ξ η r₀ c₃ N ω := by
      have := Finset.mem_range.1 hj
      omega
    exact (mgIncr_eq_inner hjlt).symm
  rw [hcongr, mid]
  ring


/-! ## 4. A measurable cap for the middle term -/

/-- **`midCap`** — `√(∑_{j<K} Δ_j²)`, which dominates `mid` and, unlike it, is a function of a
**deterministic** range, so every measurability and integrability fact about it comes straight from
`LogDetMartingale`'s per-increment exports.  Charging `midCap` rather than `mid` to the drift side
costs nothing: both have second moment at most `varBound ≈ 1.4·10⁻⁴`. -/
noncomputable def midCap (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι)
    (A₀ : EuclideanSpace ℝ (UT n)) (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n))
    (η r₀ c₃ : ℝ) (N K : ℕ) (ω : Ω) : ℝ :=
  Real.sqrt (∑ j ∈ Finset.range K, (mgIncr q W A₀ ξ η r₀ c₃ N j ω) ^ 2)

theorem midCap_nonneg {η r₀ c₃ : ℝ} {N K : ℕ} {ω : Ω} :
    0 ≤ midCap q W A₀ ξ η r₀ c₃ N K ω := Real.sqrt_nonneg _

theorem midCap_sq {η r₀ c₃ : ℝ} {N K : ℕ} {ω : Ω} :
    (midCap q W A₀ ξ η r₀ c₃ N K ω) ^ 2
      = ∑ j ∈ Finset.range K, (mgIncr q W A₀ ξ η r₀ c₃ N j ω) ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- **`mid ≤ midCap`.** -/
theorem mid_le_midCap {η r₀ c₃ : ℝ} {N K : ℕ} {ω : Ω} :
    mid q W A₀ ξ η r₀ c₃ N K ω ≤ midCap q W A₀ ξ η r₀ c₃ N K ω := by
  have hsq := mid_sq_le (q := q) (W := W) (A₀ := A₀) (ξ := ξ)
    (η := η) (r₀ := r₀) (c₃ := c₃) (N := N) (K := K) (ω := ω)
  have hcap := midCap_sq (q := q) (W := W) (A₀ := A₀) (ξ := ξ)
    (η := η) (r₀ := r₀) (c₃ := c₃) (N := N) (K := K) (ω := ω)
  have h0 : 0 ≤ midCap q W A₀ ξ η r₀ c₃ N K ω := midCap_nonneg
  nlinarith [hsq, hcap, h0]

/-- **The stopped accumulation, with a measurable drift charge.**  `mgPart … K` is the
deterministic martingale of `LogDetMartingale`; `midCap` is the extra drift charge. -/
theorem sum_Vcoef_ge {η r₀ c₃ : ℝ} {N K : ℕ} {ω : Ω} :
    mgPart q W A₀ ξ η r₀ c₃ N K ω - midCap q W A₀ ξ η r₀ c₃ N K ω
      ≤ ∑ j ∈ Finset.range (min K (tau q W A₀ ξ η r₀ c₃ N ω - 1)),
          ⟪LogDetChainLower.Vcoef q W A₀ ξ j ω, ξ j ω⟫ := by
  rw [sum_Vcoef_eq]
  linarith [mid_le_midCap (q := q) (W := W) (A₀ := A₀) (ξ := ξ)
    (η := η) (r₀ := r₀) (c₃ := c₃) (N := N) (K := K) (ω := ω)]

end Submission.L10.MidTerm


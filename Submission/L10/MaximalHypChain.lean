/-
Gate L-10 (`klartag_packing`), brief 54 — route refinement.

**The maximal inequality in `DriftStopped3.MaximalHyp`'s shape.**

Report 54 proved `E[max_{k<N} ‖ξ_k‖] ≤ σ·(√(2·log(2dN)) + 1)` with `σ = √(v·d)`.  The consumer is
`MaximalHyp ξ P N B`, "an increment read at a random index integrates to at most `B`", which is the
pointwise `GaussianMaximal.norm_at_index_le_maxNorm` followed by `integral_mono`.

`GaussianMaximal.maxNorm` is a direct recursion, not a `Finset.sup'`, so no nonemptiness side
condition propagates into the exported statement.

**The integrability hypothesis is discharged here.**  Report 54 left `Integrable (maxNorm ξ N)` as
a hypothesis; `maxNorm ξ N ≤ ∑_{k<N} ‖ξ_k‖` reduces it to integrability of each increment's norm,
which is what the drift side already assumes.
-/
import Submission.L10.GaussianMaximal
import Submission.L10.DriftStopped3
import Submission.L10.StepGlue

namespace Submission.L10

open MeasureTheory ProbabilityTheory Set Real Submission.L10.Increments
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-! ## 1. Integrability of the running maximum -/

omit [MeasurableSpace Ω] in
theorem maxNorm_le_sum {E : Type*} [NormedAddCommGroup E] {ξ : ℕ → Ω → E} (N : ℕ) (ω : Ω) :
    maxNorm ξ N ω ≤ ∑ k ∈ Finset.range N, ‖ξ k ω‖ := by
  induction N with
  | zero => simp [maxNorm]
  | succ m ih =>
    have hm : maxNorm ξ (m + 1) ω = max (maxNorm ξ m ω) ‖ξ m ω‖ := rfl
    rw [hm, Finset.sum_range_succ]
    exact max_le (by linarith [norm_nonneg (ξ m ω)]) (by
      have : (0 : ℝ) ≤ ∑ k ∈ Finset.range m, ‖ξ k ω‖ :=
        Finset.sum_nonneg fun k _ => norm_nonneg _
      linarith)

omit [IsProbabilityMeasure P] in
/-- **The integrability of the running maximum**, from the increments' norms. -/
theorem integrable_maxNorm {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    {ξ : ℕ → Ω → E} (hξ : ∀ k, Measurable (ξ k))
    (hnorm : ∀ k, Integrable (fun ω => ‖ξ k ω‖) P) (N : ℕ) :
    Integrable (maxNorm ξ N) P := by
  refine Integrable.mono' (g := fun ω => ∑ k ∈ Finset.range N, ‖ξ k ω‖)
    (integrable_finsetSum _ fun k _ => hnorm k)
    (measurable_maxNorm hξ N).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (maxNorm_nonneg N ω)]
  exact maxNorm_le_sum N ω

/-! ## 2. `MaximalHyp` -/

/-- **The maximal inequality, in the consumer's shape.**  `B = √(v·d)·(√(2·log(2·d·N)) + 1)`. -/
theorem maximalHyp_of_laws {n : ℕ} {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)} {v : ℝ≥0} {σ : ℝ}
    (hσ : 0 < σ) (hv : 0 < (v : ℝ)) (hσ2 : σ ^ 2 = (v : ℝ) * (Fintype.card (UT n) : ℝ))
    (hlaw : ∀ k, ∀ p : UT n, P.map (fun ω => ξ k ω p) = gaussianReal 0 v)
    (hξ : ∀ k, Measurable (ξ k)) (hnorm : ∀ k, Integrable (fun ω => ‖ξ k ω‖) P) (N : ℕ)
    (hK : Real.exp 1 ≤ 2 * (Fintype.card (UT n) : ℝ) * (N : ℝ)) :
    DriftStopped3.MaximalHyp ξ P N
      (σ * (Real.sqrt (2 * Real.log (2 * (Fintype.card (UT n) : ℝ) * (N : ℝ))) + 1)) := by
  have hint : Integrable (maxNorm ξ N) P := integrable_maxNorm hξ hnorm N
  have hmax : ∫ ω, maxNorm ξ N ω ∂P
      ≤ σ * (Real.sqrt (2 * Real.log (2 * (Fintype.card (UT n) : ℝ) * (N : ℝ))) + 1) :=
    expectation_max_norm_le_log hσ hv hσ2 hlaw hξ N hK hint
  intro f hf hintf
  have hmono : ∫ ω, ‖ξ (f ω) ω‖ ∂P ≤ ∫ ω, maxNorm ξ N ω ∂P :=
    integral_mono hintf hint fun ω => norm_at_index_le_maxNorm f hf ω
  exact le_trans hmono hmax

/-- **`MaximalHyp` on the chain's scaled increments.**  `chainSetup` gives `ξ_k` standard Gaussian;
the chain's increment is `√h · ξ_k`, whose coordinates are `N(0,h)` by
`StepGlue.coord_law_smul`.  The constant is

  `B = √(h·d)·(√(2·log(2·d·N)) + 1)`,  `d = card (UT n)`,

which at `h = n⁻⁹`, `d = n(n+1)/2`, `N = ⌈16·n⁷·log n⌉` is `(3√(log n) + o(√(log n)))·n^{−3.5}`. -/
theorem maximalHyp_smul {n : ℕ} {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}
    (hξ : ∀ k, Measurable (ξ k))
    (hlaw : ∀ k, P.map (ξ k) = stdGaussian (EuclideanSpace ℝ (UT n)))
    {h : ℝ} (hh : 0 < h)
    (hnorm : ∀ k, Integrable (fun ω => ‖Real.sqrt h • ξ k ω‖) P)
    (hd : 0 < Fintype.card (UT n)) (N : ℕ)
    (hK : Real.exp 1 ≤ 2 * (Fintype.card (UT n) : ℝ) * (N : ℝ)) :
    DriftStopped3.MaximalHyp (fun k ω => Real.sqrt h • ξ k ω) P N
      (Real.sqrt (h * (Fintype.card (UT n) : ℝ))
        * (Real.sqrt (2 * Real.log (2 * (Fintype.card (UT n) : ℝ) * (N : ℝ))) + 1)) := by
  have hdR : (0 : ℝ) < (Fintype.card (UT n) : ℝ) := by exact_mod_cast hd
  have hvcoe : ((Real.toNNReal h : ℝ≥0) : ℝ) = h := Real.coe_toNNReal _ hh.le
  have hσpos : 0 < Real.sqrt (h * (Fintype.card (UT n) : ℝ)) :=
    Real.sqrt_pos.2 (by positivity)
  have hvpos : (0 : ℝ) < ((Real.toNNReal h : ℝ≥0) : ℝ) := by rw [hvcoe]; exact hh
  have hσ2 : Real.sqrt (h * (Fintype.card (UT n) : ℝ)) ^ 2
      = ((Real.toNNReal h : ℝ≥0) : ℝ) * (Fintype.card (UT n) : ℝ) := by
    rw [Real.sq_sqrt (by positivity), hvcoe]
  have hveq : Real.toNNReal (Real.sqrt h ^ 2) = Real.toNNReal h := by rw [Real.sq_sqrt hh.le]
  have hcoord : ∀ k, ∀ p : UT n,
      P.map (fun ω => (Real.sqrt h • ξ k ω) p) = gaussianReal 0 (Real.toNNReal h) := by
    intro k p
    rw [← hveq]
    exact StepGlue.coord_law_smul (hξ k) (hlaw k) (Real.sqrt h) p
  have hmeas : ∀ k, Measurable (fun ω => Real.sqrt h • ξ k ω) :=
    fun k => (measurable_const_smul (Real.sqrt h)).comp (hξ k)
  exact maximalHyp_of_laws hσpos hvpos hσ2 hcoord hmeas hnorm N hK

end Submission.L10

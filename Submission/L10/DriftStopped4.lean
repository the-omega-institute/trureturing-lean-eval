import Submission.L10.DriftStopped3

/-!
# Gate L-10 (`klartag_packing`) — the stopped error over a general `B` (rule 14)

Brief 57.  Report 55 §3 said the remaining steps wait on brief 54's *number*; rule 14 says the
opposite, and rule 14 is right: the number enters only in one final numeric inequality.  This
module carries the maximal constant through symbolically.

## The split that keeps both structures

`stoppedErr` has two live cases (report 51), and they must be summed by **different** arguments:

* on the good range it is `ChainWiring.chainErr`, paid only at *freeze* steps — at most `dim E`
  of them (`Chain.card_freezes_le`), which is `ChainDrift.sum_err_le`'s shape and gives `d·2ε ≤ 8/n`
  at the adopted parameters (`ChainWiring.total_error_adopted`);
* at `k = τ − 1` it is `c‖π_kξ_k‖² − ⟪V k, ξ k⟫`, paid **once per path** — the events `{τ = k+1}`
  are disjoint, so summing reads one increment at a random index, which is `MaximalHyp`'s shape.

Collapsing the two into one pointwise bound would destroy one of the two countings, so
`stoppedErr_split` keeps them apart: each summand is `0` outside its own case.

## The coefficient

`C₁ := c + √(dim) / m` with `c = 1/(2M²(1+δ)²)` the drift's quadratic coefficient, `m = a₀ − (r₀ +
c₃η)` the state's lower bound and `M = a₀ + (r₀ + c₃η)` its upper bound: the second moment enters
with `c` and the first with `‖V k‖ ≤ √(dim)/m` (`DriftStopped2.norm_stoppedV_le`).  At the adopted
parameters — `h = n⁻⁹`, `N = ⌈16 n⁷ log n⌉`, `c₃ = n²`, `η ≤ √2·n⁻³`, `n ≥ 2 073 600` — `a₀ =
(1−1/n)⁻²` and `r₀ = 24√(log n/n)` are both `1 + o(1)`, `dim = n(n+1)/2 ≤ n²`, so `m, M → 1`,
`c → 1/2` and

    C₁ = c + √(dim)/m ≤ 1/2 + 2n  ≤  3n.

With `B ≈ √(h(dim + log N)) ≈ n^{−3.5}` that is `C₁·B ≈ 3 n^{−2.5}`, against a slack of order `1`.
-/


namespace Submission.L10.DriftStopped4

open MeasureTheory Matrix Finset Module Submission.L10 Submission.L10.Increments
open Submission.L10.StoppedChain Submission.L10.DriftStopped Submission.L10.DriftStopped2
open scoped RealInnerProductSpace

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι] {Ω : Type*} [MeasurableSpace Ω]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

/-! ## 1. The coefficient -/

/-- `C₁ = c + √(dim)/m`: the second moment enters with the drift's quadratic coefficient, the
first with the bound on `‖V k‖`. -/
noncomputable def C₁ (n : ℕ) (m c : ℝ) : ℝ := c + Real.sqrt n / m

theorem C₁_nonneg {m c : ℝ} (hc : 0 ≤ c) (hm : 0 < m) : 0 ≤ C₁ n m c := by
  rw [C₁]; positivity

/-! ## 2. The split -/

/-- **The two cases, kept apart.**  Each summand vanishes outside its own case, so the first sums
by the freeze count and the second by the disjointness of `{τ = k+1}`. -/
theorem stoppedErr_split {η a₀ r₀ c₃ c : ℝ} {N : ℕ} (hN : 1 ≤ N) (hc : 0 ≤ c)
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃) (hlt : r₀ + c₃ * η < a₀)
    (k : ℕ) (ω : Ω) :
    stoppedErr q W A₀ ξ η r₀ c₃ c N k ω
      ≤ (if k + 1 ≤ tau q W A₀ ξ η r₀ c₃ N ω - 1 then ChainWiring.chainErr q W A₀ ξ k ω else 0)
        + (if k < tau q W A₀ ξ η r₀ c₃ N ω ∧ ¬ (k + 1 ≤ tau q W A₀ ξ η r₀ c₃ N ω - 1) then
            C₁ n (a₀ - (r₀ + c₃ * η)) c * (‖ξ k ω‖ + ‖ξ k ω‖ ^ 2) else 0) := by
  have hm : 0 < a₀ - (r₀ + c₃ * η) := by linarith
  have hC : 0 ≤ C₁ n (a₀ - (r₀ + c₃ * η)) c := C₁_nonneg hc hm
  by_cases h1 : k + 1 ≤ tau q W A₀ ξ η r₀ c₃ N ω - 1
  · rw [ite_eq_left h1, ite_eq_right (by tauto), stoppedErr, ite_eq_left h1]
    simp
  · by_cases h2 : k < tau q W A₀ ξ η r₀ c₃ N ω
    · rw [ite_eq_right h1, ite_eq_left ⟨h2, h1⟩, zero_add]
      refine le_trans (stoppedErr_mid_le hN hc hA₀ hq hne hA₀m hη hr₀ hc₃ hlt h1 h2) ?_
      have hx0 : (0 : ℝ) ≤ ‖ξ k ω‖ := norm_nonneg _
      have hx2 : (0 : ℝ) ≤ ‖ξ k ω‖ ^ 2 := sq_nonneg _
      have hVle : Real.sqrt n / (a₀ - (r₀ + c₃ * η)) ≤ C₁ n (a₀ - (r₀ + c₃ * η)) c := by
        rw [C₁]; linarith
      have hcle : c ≤ C₁ n (a₀ - (r₀ + c₃ * η)) c := by
        rw [C₁]
        have : (0 : ℝ) ≤ Real.sqrt n / (a₀ - (r₀ + c₃ * η)) := by positivity
        linarith
      nlinarith [hx0, hx2, hVle, hcle]
    · rw [ite_eq_right h1, ite_eq_right (by tauto), stoppedErr, ite_eq_right h1, ite_eq_right h2]
      simp

/-! ## 3. The maximal hypothesis, both moments -/

/-- **Brief 54's input, over a general `B`** — both moments at a random index, since the middle
case carries `‖ξ‖` and `‖ξ‖²`.  `B` is a single constant by taking the larger of the two; brief 54's
`E[max_{k<N}‖ξ_k‖]` bounds the first and its square the second. -/
def MaximalHyp2 (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (P : Measure Ω) (N : ℕ) (B : ℝ) : Prop :=
  ∀ f : Ω → ℕ, (∀ ω, f ω < N) →
    Integrable (fun ω => ‖ξ (f ω) ω‖) P → Integrable (fun ω => ‖ξ (f ω) ω‖ ^ 2) P →
    ∫ ω, ‖ξ (f ω) ω‖ ∂P ≤ B ∧ ∫ ω, ‖ξ (f ω) ω‖ ^ 2 ∂P ≤ B

theorem maximalHyp2_of (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (P : Measure Ω) (N : ℕ) {B : ℝ}
    (h : MaximalHyp2 ξ P N B) {f : Ω → ℕ} (hf : ∀ ω, f ω < N)
    (h1 : Integrable (fun ω => ‖ξ (f ω) ω‖) P) (h2 : Integrable (fun ω => ‖ξ (f ω) ω‖ ^ 2) P) :
    ∫ ω, (‖ξ (f ω) ω‖ + ‖ξ (f ω) ω‖ ^ 2) ∂P ≤ 2 * B := by
  obtain ⟨ha, hb⟩ := h f hf h1 h2
  rw [integral_add h1 h2]
  linarith


/-! ## 4. The hypothesis brief 54 must discharge -/

/-- **Brief 54's obligation, at the adopted parameters and over a general `B`.**  `N` is
`ParamsAdopted2.numStepsAdopted2 n = ⌈16 n⁷ log n⌉`; `ξ` is the chain's driving sequence on
`ChainSetup`, at scale `√h` with `h = ParamsAdopted2.stepSizeAdopted2 n ≤ n⁻⁹`.  Its expected value
is `B ≈ √(h·(dim + log N)) ≈ n^{−3.5}`. -/
def MaximalAtAdopted (P : Measure Ω) (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (B : ℝ) : Prop :=
  MaximalHyp2 ξ P (ParamsAdopted2.numStepsAdopted2 n) B

/-- **The numeric side condition** the value of `B` closes: the middle case's total, `C₁·2B`, must
fit the slack the existence step has.  With `C₁ ≤ 3n` and `B ≈ n^{−3.5}` this is `≈ 6 n^{−2.5}`. -/
def SlackHyp (n : ℕ) (m c B slack : ℝ) : Prop := C₁ n m c * (2 * B) ≤ slack

/-- The two together, in the shape `driftSide_of_maximal` consumes. -/
def Brief54Obligation (P : Measure Ω) (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n))
    (m c B slack : ℝ) : Prop :=
  MaximalAtAdopted P ξ B ∧ SlackHyp n m c B slack

end Submission.L10.DriftStopped4

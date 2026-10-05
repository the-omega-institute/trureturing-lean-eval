import Submission.L10.ChainErrBudget
import Submission.L10.FreeDimTotal
import Submission.L10.DriftStopped6d
import Submission.L10.TerminalRatio

/-!
# Gate L-10 (`klartag_packing`), brief 93 — the drift bound with the **accumulated** error total

Report 88 measured the cost of report 57 §1's accounting.  `DriftStopped5.sum_good_le` bounds the
good-range total by `dim E · ε` — a *per-step* bound `ε`, charged once per frozen direction — and
with the only per-step bound the tree can prove, `ε = c₃η/m`, that overshoots
`ChainWiring.total_error_adopted`'s `8/n` for every `c₃ > 7.49`.

But the lift is paid once per **contact**, not once per direction: the freezes partition the active
set (`Chain.sum_card_newActive`), so `∑_{k<K} chainErr k ω ≤ |C_K|·η/m ≤ c₃η/m`
(`ChainErrBudget.sum_chainErr_le_of_lt_tau`) — **one `ε` in total**, not `dim E` of them.  This
module re-threads the drift side on that total.

## Contents

1. `sum_good_le_of_prefix` — the good-range total from a *prefix-sum* hypothesis `hpre`, general in
   `q`.  The indicator `k + 1 ≤ τ ω − 1` cuts `range m` to `range (min m (τ ω − 1))`, and that
   index is below `τ`, so one application of `hpre` finishes.  No freeze count appears.
2. `sum_stoppedErr_le_acc`, `integral_sum_stoppedErr_le_acc`, `sum_integral_stoppedErr_le_acc` —
   `DriftStopped5.sum_stoppedErr_le` and `DriftStopped6.integral_sum_stoppedErr_le` with `dim E · ε`
   replaced by `E`.  The middle case is untouched: still one increment at `τ − 1`, still `C₁ · 2B`.
3. `drift_bound_stopped_acc` — **a re-instantiation, not a re-proof**: `DriftStopped6.logdet_bound_sum'`
   (`:309`) and `DriftStopped6.drift_bound_stopped` (`:324`) already take the error total `E` as an
   input; only `DriftStopped6.drift_bound_stopped_maximal` (`:341`) hard-wires `dim E · ε` by
   feeding them `sum_integral_stoppedErr_le`.  Swapping that one argument is the whole change.
4. `driftRHS_acc`, `drift_bound_at_acc`, `goodPathAt_acc`, `goodPathAt_of_S_acc` — the same swap
   carried to `GoodPathBounds.goodPathAt_of_S` (`:819`).  `driftRHS n A₀ c₃ ε S` is
   `driftRHS_acc n A₀ c₃ (dim E · ε) S` definitionally (`driftRHS_eq`), so nothing downstream of
   the RHS changes shape.
5. `EaccAt` and the numbers at `c₃'' = n^{11/4}` (`FinalDischarge2.c3Adopted''`).

**Binder diff, `goodPathAt_of_S_acc` against `GoodPathBounds.goodPathAt_of_S`:** `hε` and `hbdabs`
are **gone** — both budgets are proved inside, from the parameters — and `hbudget` reads
`driftRHS_acc … (EaccAt (m+1) c₃) S` where it read `driftRHS … ε S`.  Every other binder is
identical.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Submission.L10.DriftAccumulated

open MeasureTheory Matrix Finset Module
open scoped NNReal RealInnerProductSpace
open Submission.L10 Submission.L10.Increments
open Submission.L10.StoppedChain Submission.L10.DriftStopped
open Submission.L10.DriftInputsStopped Submission.L10.StateInvariant

/-! ## 1. The good-range total from a prefix-sum bound -/

section Good

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι] {Ω : Type*} [m0 : MeasurableSpace Ω]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

/-- **`DriftStopped5.sum_good_le` with the freeze count removed.**  The indicator restricts the sum
to `k < τ ω − 1`, i.e. to `Finset.range (min m (τ ω − 1))`, and that index is `< τ ω`; so a single
prefix-sum bound at one index replaces "`dim E` freezes, each costing `ε`". -/
theorem sum_good_le_of_prefix {η r₀ c₃ E : ℝ} {N m : ℕ} {ω : Ω} (hN : 1 ≤ N)
    (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃)
    (hpre : ∀ K, K < tau q W A₀ ξ η r₀ c₃ N ω →
      ∑ k ∈ Finset.range K, ChainWiring.chainErr q W A₀ ξ k ω ≤ E) :
    ∑ k ∈ Finset.range m,
        (if k + 1 ≤ tau q W A₀ ξ η r₀ c₃ N ω - 1
          then ChainWiring.chainErr q W A₀ ξ k ω else 0)
      ≤ E := by
  classical
  have hτ1 : 1 ≤ tau q W A₀ ξ η r₀ c₃ N ω :=
    one_le_tau (q := q) (W := W) (A₀ := A₀) (ξ := ξ) (η := η) (r₀ := r₀) (c₃ := c₃) hN hr₀ hc₃ ω
  have h1 : ∑ k ∈ Finset.range m,
        (if k + 1 ≤ tau q W A₀ ξ η r₀ c₃ N ω - 1
          then ChainWiring.chainErr q W A₀ ξ k ω else 0)
      = ∑ k ∈ (Finset.range m).filter
          (fun k => k + 1 ≤ tau q W A₀ ξ η r₀ c₃ N ω - 1),
          ChainWiring.chainErr q W A₀ ξ k ω :=
    (Finset.sum_filter _ _).symm
  have h2 : (Finset.range m).filter (fun k => k + 1 ≤ tau q W A₀ ξ η r₀ c₃ N ω - 1)
      = Finset.range (min m (tau q W A₀ ξ η r₀ c₃ N ω - 1)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]
    omega
  rw [h1, h2]
  exact hpre _ (by omega)

/-- **`DriftStopped5.sum_stoppedErr_le` with the accumulated total.**  Only the good-range summand
changes; the middle case is still one increment read at `τ − 1`. -/
theorem sum_stoppedErr_le_acc {η a₀ r₀ c₃ c E : ℝ} {N m : ℕ} {ω : Ω} (hN : 1 ≤ N) (hc : 0 ≤ c)
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃) (hlt : r₀ + c₃ * η < a₀)
    (hpre : ∀ K, K < tau q W A₀ ξ η r₀ c₃ N ω →
      ∑ k ∈ Finset.range K, ChainWiring.chainErr q W A₀ ξ k ω ≤ E) :
    ∑ k ∈ Finset.range m, stoppedErr q W A₀ ξ η r₀ c₃ c N k ω
      ≤ E + DriftStopped4.C₁ n (a₀ - (r₀ + c₃ * η)) c
          * (‖ξ (tau q W A₀ ξ η r₀ c₃ N ω - 1) ω‖
              + ‖ξ (tau q W A₀ ξ η r₀ c₃ N ω - 1) ω‖ ^ 2) := by
  classical
  have hm : 0 < a₀ - (r₀ + c₃ * η) := by linarith
  have hC : 0 ≤ DriftStopped4.C₁ n (a₀ - (r₀ + c₃ * η)) c := DriftStopped4.C₁_nonneg hc hm
  have hτ1 : 1 ≤ tau q W A₀ ξ η r₀ c₃ N ω :=
    one_le_tau (q := q) (W := W) (A₀ := A₀) (ξ := ξ) (η := η) (r₀ := r₀) (c₃ := c₃) hN hr₀ hc₃ ω
  have hsplit : ∀ k, stoppedErr q W A₀ ξ η r₀ c₃ c N k ω
      ≤ (if k + 1 ≤ tau q W A₀ ξ η r₀ c₃ N ω - 1
          then ChainWiring.chainErr q W A₀ ξ k ω else 0)
        + (if k < tau q W A₀ ξ η r₀ c₃ N ω ∧ ¬ (k + 1 ≤ tau q W A₀ ξ η r₀ c₃ N ω - 1) then
            DriftStopped4.C₁ n (a₀ - (r₀ + c₃ * η)) c * (‖ξ k ω‖ + ‖ξ k ω‖ ^ 2) else 0) := fun k =>
    DriftStopped4.stoppedErr_split hN hc hA₀ hq hne hA₀m hη hr₀ hc₃ hlt k ω
  refine le_trans (Finset.sum_le_sum fun k _ => hsplit k) ?_
  rw [Finset.sum_add_distrib]
  refine add_le_add (sum_good_le_of_prefix hN hr₀ hc₃ hpre) ?_
  rw [DriftStopped5.sum_mid_eq (q := q) (W := W) (A₀ := A₀) (ξ := ξ)
    (fun k => DriftStopped4.C₁ n (a₀ - (r₀ + c₃ * η)) c * (‖ξ k ω‖ + ‖ξ k ω‖ ^ 2)) hτ1]
  split
  · exact le_rfl
  · have hpos : (0 : ℝ) ≤ DriftStopped4.C₁ n (a₀ - (r₀ + c₃ * η)) c
        * (‖ξ (tau q W A₀ ξ η r₀ c₃ N ω - 1) ω‖
            + ‖ξ (tau q W A₀ ξ η r₀ c₃ N ω - 1) ω‖ ^ 2) := by positivity
    linarith

end Good

/-! ## 2. The accumulated total, integrated -/

section Integral

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι] {Ω : Type*} [m0 : MeasurableSpace Ω]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- **`DriftStopped6.integral_sum_stoppedErr_le` with the accumulated total.** -/
theorem integral_sum_stoppedErr_le_acc (ℱ : Filtration ℕ m0)
    {η a₀ r₀ c₃ c E B : ℝ} {N m : ℕ}
    (hG : ∀ k, MeasurableSet[ℱ k] (stateGood q W A₀ ξ η r₀ c₃ k))
    (hN : 1 ≤ N) (hc : 0 ≤ c) (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃) (hlt : r₀ + c₃ * η < a₀)
    (hpre : ∀ ω : Ω, ∀ K, K < tau q W A₀ ξ η r₀ c₃ N ω →
      ∑ k ∈ Finset.range K, ChainWiring.chainErr q W A₀ ξ k ω ≤ E)
    (hsum : Integrable
      (fun ω => ∑ k ∈ Finset.range m, stoppedErr q W A₀ ξ η r₀ c₃ c N k ω) P)
    (hmax : DriftStopped4.MaximalHyp2 ξ P N B) (hidx : DriftStopped5.IntegrableAtIndex P ξ N) :
    ∫ ω, (∑ k ∈ Finset.range m, stoppedErr q W A₀ ξ η r₀ c₃ c N k ω) ∂P
      ≤ E + DriftStopped4.C₁ n (a₀ - (r₀ + c₃ * η)) c * (2 * B) := by
  have hmeasf : Measurable (fun ω => tau q W A₀ ξ η r₀ c₃ N ω - 1) :=
    DriftStopped5.measurable_tau_sub_one ℱ hG N
  have hltN : ∀ ω, tau q W A₀ ξ η r₀ c₃ N ω - 1 < N := by
    intro ω
    have := tau_le (q := q) (W := W) (A₀ := A₀) (ξ := ξ) (η := η) (r₀ := r₀) (c₃ := c₃)
      (N := N) ω
    omega
  obtain ⟨hi1, hi2⟩ := hidx _ hmeasf hltN
  have hm : 0 < a₀ - (r₀ + c₃ * η) := by linarith
  have hC : 0 ≤ DriftStopped4.C₁ n (a₀ - (r₀ + c₃ * η)) c := DriftStopped4.C₁_nonneg hc hm
  have hrhsInt : Integrable (fun ω => E
      + DriftStopped4.C₁ n (a₀ - (r₀ + c₃ * η)) c
        * (‖ξ (tau q W A₀ ξ η r₀ c₃ N ω - 1) ω‖
            + ‖ξ (tau q W A₀ ξ η r₀ c₃ N ω - 1) ω‖ ^ 2)) P :=
    (integrable_const _).add ((hi1.add hi2).const_mul _)
  have hmono := integral_mono hsum hrhsInt (fun ω =>
    sum_stoppedErr_le_acc hN hc hA₀ hq hne hA₀m hη hr₀ hc₃ hlt (hpre ω))
  have hEq : ∫ ω, (E
        + DriftStopped4.C₁ n (a₀ - (r₀ + c₃ * η)) c
          * (‖ξ (tau q W A₀ ξ η r₀ c₃ N ω - 1) ω‖
              + ‖ξ (tau q W A₀ ξ η r₀ c₃ N ω - 1) ω‖ ^ 2)) ∂P
      = E + DriftStopped4.C₁ n (a₀ - (r₀ + c₃ * η)) c
          * ∫ ω, (‖ξ (tau q W A₀ ξ η r₀ c₃ N ω - 1) ω‖
              + ‖ξ (tau q W A₀ ξ η r₀ c₃ N ω - 1) ω‖ ^ 2) ∂P :=
    DriftStopped6.integral_affine (hi1.add hi2)
  rw [hEq] at hmono
  have hmaxb := DriftStopped4.maximalHyp2_of ξ P N hmax hltN hi1 hi2
  nlinarith [hmono, hmaxb, hC]

/-- **`DriftStopped6.sum_integral_stoppedErr_le` with the accumulated total** — the shape
`ChainDrift.drift_bound` consumes. -/
theorem sum_integral_stoppedErr_le_acc (ℱ : Filtration ℕ m0)
    {η a₀ r₀ c₃ c E B : ℝ} {N m : ℕ}
    (hG : ∀ k, MeasurableSet[ℱ k] (stateGood q W A₀ ξ η r₀ c₃ k))
    (hN : 1 ≤ N) (hc : 0 ≤ c) (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃) (hlt : r₀ + c₃ * η < a₀)
    (hpre : ∀ ω : Ω, ∀ K, K < tau q W A₀ ξ η r₀ c₃ N ω →
      ∑ k ∈ Finset.range K, ChainWiring.chainErr q W A₀ ξ k ω ≤ E)
    (hint : ∀ k ∈ Finset.range m, Integrable (stoppedErr q W A₀ ξ η r₀ c₃ c N k) P)
    (hmax : DriftStopped4.MaximalHyp2 ξ P N B) (hidx : DriftStopped5.IntegrableAtIndex P ξ N) :
    ∑ k ∈ Finset.range m, ∫ ω, stoppedErr q W A₀ ξ η r₀ c₃ c N k ω ∂P
      ≤ E + DriftStopped4.C₁ n (a₀ - (r₀ + c₃ * η)) c * (2 * B) := by
  rw [← integral_finsetSum _ hint]
  exact integral_sum_stoppedErr_le_acc ℱ hG hN hc hA₀ hq hne hA₀m hη hr₀ hc₃ hlt hpre
    (integrable_finsetSum _ hint) hmax hidx

/-- **`DriftStopped6.drift_bound_stopped_maximal` with the accumulated total.**  This is a
*re-instantiation*: `DriftStopped6.drift_bound_stopped` already takes the error total `E` as an
input, so only the argument supplied for it changes. -/
theorem drift_bound_stopped_acc {ℱ : Filtration ℕ m0}
    {η a₀ r₀ c₃ c κ E B S : ℝ} {N m : ℕ}
    (hin : ChainDrift.DriftInputs P ⇑ℱ (stoppedLogDet q W A₀ ξ η r₀ c₃ N)
      (DriftStopped6.stoppedFreeDim q W A₀ ξ η r₀ c₃ N)
      (errCond P ⇑ℱ q W A₀ ξ η r₀ c₃ c N) κ m)
    (hG : ∀ k, MeasurableSet[ℱ k] (stateGood q W A₀ ξ η r₀ c₃ k))
    (hκ : 0 ≤ κ)
    (hS : S ≤ ∑ k ∈ Finset.range m, ∫ ω,
      DriftStopped6.stoppedFreeDim q W A₀ ξ η r₀ c₃ N k ω ∂P)
    (hN : 1 ≤ N) (hc : 0 ≤ c) (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃) (hlt : r₀ + c₃ * η < a₀)
    (hpre : ∀ ω : Ω, ∀ K, K < tau q W A₀ ξ η r₀ c₃ N ω →
      ∑ k ∈ Finset.range K, ChainWiring.chainErr q W A₀ ξ k ω ≤ E)
    (hint : ∀ k ∈ Finset.range m, Integrable (stoppedErr q W A₀ ξ η r₀ c₃ c N k) P)
    (hmax : DriftStopped4.MaximalHyp2 ξ P N B) (hidx : DriftStopped5.IntegrableAtIndex P ξ N) :
    ∫ ω, stoppedLogDet q W A₀ ξ η r₀ c₃ N m ω ∂P
      ≤ ∫ ω, stoppedLogDet q W A₀ ξ η r₀ c₃ N 0 ω ∂P - κ * S
        + (E + DriftStopped4.C₁ n (a₀ - (r₀ + c₃ * η)) c * (2 * B)) :=
  DriftStopped6.drift_bound_stopped hin hκ hS
    (sum_integral_stoppedErr_le_acc ℱ hG hN hc hA₀ hq hne hA₀m hη hr₀ hc₃ hlt hpre hint hmax hidx)

end Integral

/-! ## 3. The adopted parameters, at a free contact threshold -/

section At

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}

/-- **`GoodPathBounds.driftRHS` with the error total free.**  `driftRHS n A₀ c₃ ε S` is
`driftRHS_acc n A₀ c₃ (dim E · ε) S` definitionally (`driftRHS_eq`). -/
noncomputable def driftRHS_acc (n : ℕ) (A₀ : EuclideanSpace ℝ (UT n)) (c₃ E S : ℝ) : ℝ :=
  ChainWiring.logDet A₀ - (GoodPathBounds.cqAt n c₃ * Submission.L10.cAdopted n ^ 2) * S
    + (E + DriftStopped4.C₁ n (GoodPathBounds.mAt n c₃) (GoodPathBounds.cqAt n c₃)
        * (2 * Submission.L10.B_adopted n))

theorem driftRHS_eq (n : ℕ) (A₀ : EuclideanSpace ℝ (UT n)) (c₃ ε S : ℝ) :
    GoodPathBounds.driftRHS n A₀ c₃ ε S
      = driftRHS_acc n A₀ c₃ ((finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) * ε) S := rfl

/-- **`GoodPathBounds.drift_bound_at` with the accumulated total** — `hε`/`hbd` replaced by the
prefix-sum hypothesis, `dim E · ε` by `E`.  Everything else is the frozen proof. -/
theorem drift_bound_at_acc (hn : 2073600 ≤ n) {c₃ E S : ℝ} {m : ℕ}
    (hc₃0 : 0 ≤ c₃) (hc₃η : c₃ * DriftStopped6.etaAdopted n ≤ 1 / 4)
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a0C n • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hinterr : ∀ k, Integrable
      (stoppedErr q W A₀ (ChainSetup.step (Submission.L10.cAdopted n))
        (DriftStopped6.etaAdopted n) (DriftStopped6.r0Adopted n) c₃ (GoodPathBounds.cqAt n c₃)
        (ParamsAdopted2.numStepsAdopted2 n) k)
      (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))))
    (hS : S ≤ ∑ k ∈ Finset.range m, ∫ ω,
      DriftStopped6.stoppedFreeDim q W A₀ (ChainSetup.step (Submission.L10.cAdopted n))
        (DriftStopped6.etaAdopted n) (DriftStopped6.r0Adopted n) c₃
        (ParamsAdopted2.numStepsAdopted2 n) k ω
      ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))))
    (hpre : ∀ ω, ∀ K, K < tau q W A₀ (ChainSetup.step (Submission.L10.cAdopted n))
        (DriftStopped6.etaAdopted n) (DriftStopped6.r0Adopted n) c₃
        (ParamsAdopted2.numStepsAdopted2 n) ω →
      ∑ k ∈ Finset.range K, ChainWiring.chainErr q W A₀
        (ChainSetup.step (Submission.L10.cAdopted n)) k ω ≤ E) :
    ∫ ω, stoppedLogDet q W A₀ (ChainSetup.step (Submission.L10.cAdopted n))
        (DriftStopped6.etaAdopted n) (DriftStopped6.r0Adopted n) c₃
        (ParamsAdopted2.numStepsAdopted2 n) m ω
        ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))
      ≤ ∫ ω, stoppedLogDet q W A₀ (ChainSetup.step (Submission.L10.cAdopted n))
          (DriftStopped6.etaAdopted n) (DriftStopped6.r0Adopted n) c₃
          (ParamsAdopted2.numStepsAdopted2 n) 0 ω
          ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))
        - (GoodPathBounds.cqAt n c₃ * Submission.L10.cAdopted n ^ 2) * S
        + (E + DriftStopped4.C₁ n (GoodPathBounds.mAt n c₃) (GoodPathBounds.cqAt n c₃)
            * (2 * Submission.L10.B_adopted n)) := by
  have hn3 : 3 ≤ n := by omega
  have hN : 1 ≤ ParamsAdopted2.numStepsAdopted2 n := by
    have := Submission.L10.three_le_numStepsAdopted2 hn3; omega
  have hG : ∀ k, MeasurableSet[ChainSetup.filtration (F := EuclideanSpace ℝ (UT n)) k]
      (stateGood q W A₀ (ChainSetup.step (Submission.L10.cAdopted n))
        (DriftStopped6.etaAdopted n) (DriftStopped6.r0Adopted n) c₃ k) :=
    fun k => measurableSet_stateGood_step _ _ _ _ k
  have hlt := GoodPathBounds.lt_a0C_of_mAt hn hc₃η
  have hcq0 := GoodPathBounds.cqAt_nonneg hn hc₃η hc₃0
  have hκ : (0 : ℝ) ≤ GoodPathBounds.cqAt n c₃ * Submission.L10.cAdopted n ^ 2 := by positivity
  have hrec := driftInputs_stopped (q := q) (W := W) (A₀ := A₀) (m := m) hN hA₀ hq hne hA₀m
    (DriftStopped7.etaAdopted_nonneg (n := n)) (DriftStopped7.r0Adopted_nonneg (n := n)) hc₃0 hlt
    (le_of_eq (by rw [GoodPathBounds.deltaAt, GoodPathBounds.mAt]))
    (GoodPathBounds.deltaAt_nonneg hn hc₃η) (GoodPathBounds.deltaAt_lt_one hn hc₃η)
    (by rw [GoodPathBounds.cqAt, GoodPathBounds.MAt]) hinterr
  exact drift_bound_stopped_acc
    (ℱ := ChainSetup.filtration (F := EuclideanSpace ℝ (UT n)))
    hrec hG hκ hS hN hcq0 hA₀ hq hne hA₀m
    (DriftStopped7.etaAdopted_nonneg (n := n)) (DriftStopped7.r0Adopted_nonneg (n := n))
    hc₃0 hlt hpre (fun k _ => hinterr k)
    (Submission.L10.maximalAtAdopted_adopted hn3)
    (Submission.L10.integrableAtIndex_adopted hn3)

end At

/-! ## 4. The accumulated total at the adopted parameters, and the existence step -/

section Assembly

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}

/-- **`E_acc`** — the accumulated discretisation total, `c₃·η/m`.  Numerically this is report 88's
per-step `ε`; what changes is that the drift bound charges it **once**, not `dim E` times. -/
noncomputable def EaccAt (n : ℕ) (c₃ : ℝ) : ℝ := ChainErrBudget.epsAt n c₃

theorem EaccAt_eq (n : ℕ) (c₃ : ℝ) :
    EaccAt n c₃ = c₃ * (DriftStopped6.etaAdopted n / GoodPathBounds.mAt n c₃) := rfl

/-- **The prefix-sum hypothesis, discharged.**  `ChainErrBudget.sum_chainErr_le_of_lt_tau` gives
`|C_K|·η/m`; `stateGood K` (available because `K < τ`) gives `|C_K| ≤ c₃`. -/
theorem sum_chainErr_le_c3 {Ω : Type*} [MeasurableSpace Ω] {xs : ι → (Fin n → ℝ)}
    {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)} {η a₀ r₀ c₃ : ℝ} {N K : ℕ} {ω : Ω}
    (hA₀ : A₀ ∈ Chain.kSet (fun i => ChainWiring.qUT (xs i)) W)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃)
    (hlt : r₀ + c₃ * η < a₀) (hδ1 : c₃ * η < a₀ - (r₀ + c₃ * η))
    (hK : K < tau (fun i => ChainWiring.qUT (xs i)) W A₀ ξ η r₀ c₃ N ω) :
    ∑ k ∈ Finset.range K,
        ChainWiring.chainErr (fun i => ChainWiring.qUT (xs i)) W A₀ ξ k ω
      ≤ c₃ * (η / (a₀ - (r₀ + c₃ * η))) := by
  refine le_trans
    (ChainErrBudget.sum_chainErr_le_of_lt_tau hA₀ hA₀m hη hr₀ hc₃ hlt hδ1 hK) ?_
  obtain ⟨-, -, hcnt⟩ := stateGood_of_lt_tau (N := N)
    (q := fun i => ChainWiring.qUT (xs i)) (W := W) (A₀ := A₀) (ξ := ξ)
    (η := η) (r₀ := r₀) (c₃ := c₃) hK
  have hm : 0 < a₀ - (r₀ + c₃ * η) := by linarith
  exact mul_le_mul_of_nonneg_right hcnt (by positivity)

/-- **`GoodPathBounds.goodPathAt` on the accumulated total.**  `hbdabs'` is report 88's restricted
two-sided budget (it feeds integrability only), `hpre` the prefix-sum bound (it feeds the drift),
and the conclusion's right-hand side is `driftRHS_acc`, with `E` in place of `dim E · ε`. -/
theorem goodPathAt_acc (hn : 2073600 ≤ n) {c₃ ε E S b pcnt r : ℝ} (hr : 0 < r)
    (hc₃0 : 0 ≤ c₃) (hc₃η : c₃ * DriftStopped6.etaAdopted n ≤ 1 / 4)
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a0C n • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hε : 0 ≤ ε)
    (hbdabs : ChainErrBudget.StoppedErrBudget q W A₀
      (ChainSetup.step (Submission.L10.cAdopted n)) (DriftStopped6.etaAdopted n)
      (DriftStopped6.r0Adopted n) c₃ (ParamsAdopted2.numStepsAdopted2 n) ε)
    (hpre : ∀ ω, ∀ K, K < tau q W A₀ (ChainSetup.step (Submission.L10.cAdopted n))
        (DriftStopped6.etaAdopted n) (DriftStopped6.r0Adopted n) c₃
        (ParamsAdopted2.numStepsAdopted2 n) ω →
      ∑ k ∈ Finset.range K, ChainWiring.chainErr q W A₀
        (ChainSetup.step (Submission.L10.cAdopted n)) k ω ≤ E)
    (hS : S ≤ ∑ k ∈ Finset.range (ParamsAdopted2.numStepsAdopted2 n - 1), ∫ ω,
      DriftStopped6.stoppedFreeDim q W A₀ (ChainSetup.step (Submission.L10.cAdopted n))
        (DriftStopped6.etaAdopted n) (DriftStopped6.r0Adopted n) c₃
        (ParamsAdopted2.numStepsAdopted2 n) k ω
      ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))))
    (hcnt : (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))).real
        (StateInvariant4.countGood q W A₀ (ChainSetup.step (Submission.L10.cAdopted n))
          (ParamsAdopted2.numStepsAdopted2 n) c₃)ᶜ ≤ pcnt)
    (hLb : GoodPathBounds.logDetLow n c₃ < b)
    (hbudget : (driftRHS_acc n A₀ c₃ E S - GoodPathBounds.logDetLow n c₃)
        / (b - GoodPathBounds.logDetLow n c₃)
      + GoodPathBounds.failTotal n pcnt < 1) :
    ∃ ω, ω ∈ StateInvariant4.wiredGood' r (ChainSetup.coord 0)
        (ChainSetup.step (Submission.L10.cAdopted n)) (6 * r * 1 * Real.sqrt n)
        (ParamsAdopted2.numStepsAdopted2 n) (DriftStopped6.etaAdopted n) q W A₀
        (DriftStopped6.r0Adopted n) c₃ ∧
      ChainWiring.logDet (Chain.chain q W A₀ (ChainSetup.step (Submission.L10.cAdopted n))
        (ParamsAdopted2.numStepsAdopted2 n - 1) ω).1 ≤ b := by
  have hn3 : 3 ≤ n := by omega
  have hN : 1 ≤ ParamsAdopted2.numStepsAdopted2 n := by
    have := Submission.L10.three_le_numStepsAdopted2 hn3; omega
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
  have hdrift := drift_bound_at_acc (q := q) (W := W) (A₀ := A₀)
    (m := ParamsAdopted2.numStepsAdopted2 n - 1)
    hn hc₃0 hc₃η hA₀ hq hne hA₀m hinterr hS hpre
  have hzero : ∫ ω, stoppedLogDet q W A₀ (ChainSetup.step (Submission.L10.cAdopted n))
        (DriftStopped6.etaAdopted n) (DriftStopped6.r0Adopted n) c₃
        (ParamsAdopted2.numStepsAdopted2 n) 0 ω
        ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))
      = ChainWiring.logDet A₀ := by
    simp only [GoodPathBounds.stoppedLogDet_zero]
    simp
  rw [hzero] at hdrift
  have hfail : (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))).real
      (StateInvariant4.wiredGood' r (ChainSetup.coord 0)
        (ChainSetup.step (Submission.L10.cAdopted n)) (6 * r * 1 * Real.sqrt n)
        (ParamsAdopted2.numStepsAdopted2 n) (DriftStopped6.etaAdopted n) q W A₀
        (DriftStopped6.r0Adopted n) c₃)ᶜ ≤ GoodPathBounds.failTotal n pcnt := by
    refine le_trans (StateInvariant4.measureReal_compl_wiredGood'_le _ _ _ _ _ _ _) ?_
    rw [GoodPathBounds.failTotal]
    have h1 := GoodPathBounds.chainGood_failure (n := n) hn3 hr
    have h2 := GoodPathBounds.accGood_failure (q := q) (W := W) (A₀ := A₀) hn3
    linarith [hcnt]
  refine DriftStopped6.exists_logDet_le_on_wiredGood' (le_refl _) ?_
  refine GoodPathBounds.exists_mem_of_integral_le
    (DriftStopped6.measurable_stoppedLogDet hξm hτ _)
    (DriftStopped6.integrable_stoppedLogDet hN hξm hτ hA₀ hq hne hA₀m
      (DriftStopped7.etaAdopted_nonneg (n := n)) (DriftStopped7.r0Adopted_nonneg (n := n))
      hc₃0 hlt _)
    (L := GoodPathBounds.logDetLow n c₃) (B := driftRHS_acc n A₀ c₃ E S)
    (fun ω => GoodPathBounds.stoppedLogDet_ge hN hA₀ hq hne hA₀m
      (DriftStopped7.etaAdopted_nonneg (n := n)) (DriftStopped7.r0Adopted_nonneg (n := n))
      hc₃0 hlt _ ω)
    hdrift
    (GoodPathBounds.measurableSet_wiredGood' hξm (ChainSetup.measurable_coord 0) _ _ _ _ _ _)
    hfail hLb hbudget

end Assembly

/-! ## 5. The deliverable: `GoodPathBounds.GoodPathAt` with no freeze-budget binder -/

section GoodPathFree

open Submission.L10.ConstructionA Submission.L10.Tiling Submission.L10.PaddedLawSetupR
open Submission.L10.RawDataInst2R Submission.L10.RawDataInst2 Submission.L10.DriftStopped8R

variable {p m : ℕ} {α C' : ℝ} {g : Fin (m + 1) → ZMod p}

/-- **`GoodPathBounds.goodPathAt_of_S` with the accumulated total, and with the freeze budget
discharged.**  Binder diff against `goodPathAt_of_S` (`GoodPathBounds.lean:819`):

* **removed** `(hε : 0 ≤ ε)` and
  `(hbdabs : ∀ ω, ∀ k, |ChainWiring.chainErr (qC α) (windowOfR α p m g) (A0C (m + 1))
      (ChainSetup.step (Submission.L10.cAdopted (m + 1))) k ω| ≤ ε)` — the unprovable all-paths
  budget (report 88 §4).  Both the restricted two-sided budget and the prefix-sum bound are proved
  here from the parameters, at `ε = E = EaccAt (m + 1) c₃`;
* **changed** `hbudget`, which reads `driftRHS_acc (m+1) (A0C (m+1)) c₃ (EaccAt (m+1) c₃) S` where
  it read `driftRHS (m+1) (A0C (m+1)) c₃ ε S` — one `E` instead of `dim E · ε`.

Every other binder — `hm`, `hraw`, `hc₃0`, `hc₃η`, `hS`, `hcnt`, `hLb` — is identical, and the
conclusion is the same `GoodPathBounds.GoodPathAt p m α g c₃ C'`. -/
theorem goodPathAt_of_S_acc (hm : Threshold2.n₁ ≤ m) {R : ℝ}
    (hraw : RawDataR p (m + 1) α R (qC α) (shellR α (m + 1)) (A0C (m + 1)))
    {c₃ S pcnt : ℝ} (hc₃0 : 0 ≤ c₃)
    (hc₃η : c₃ * DriftStopped6.etaAdopted (m + 1) ≤ 1 / 4)
    (hS : S ≤ ∑ k ∈ Finset.range (ParamsAdopted2.numStepsAdopted2 (m + 1) - 1), ∫ ω,
      DriftStopped6.stoppedFreeDim (qC α) (windowOfR α p m g) (A0C (m + 1))
        (ChainSetup.step (Submission.L10.cAdopted (m + 1)))
        (DriftStopped6.etaAdopted (m + 1)) (DriftStopped6.r0Adopted (m + 1)) c₃
        (ParamsAdopted2.numStepsAdopted2 (m + 1)) k ω
      ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT (m + 1)))))
    (hcnt : (ChainSetup.gaussPath (EuclideanSpace ℝ (UT (m + 1)))).real
        (StateInvariant4.countGood (qC α) (windowOfR α p m g) (A0C (m + 1))
          (ChainSetup.step (Submission.L10.cAdopted (m + 1)))
          (ParamsAdopted2.numStepsAdopted2 (m + 1)) c₃)ᶜ ≤ pcnt)
    (hLb : GoodPathBounds.logDetLow (m + 1) c₃ < C' - 4 * Real.log ((m + 1 : ℕ) : ℝ))
    (hbudget : (driftRHS_acc (m + 1) (A0C (m + 1)) c₃ (EaccAt (m + 1) c₃) S
          - GoodPathBounds.logDetLow (m + 1) c₃)
        / ((C' - 4 * Real.log ((m + 1 : ℕ) : ℝ)) - GoodPathBounds.logDetLow (m + 1) c₃)
      + GoodPathBounds.failTotal (m + 1) pcnt < 1) :
    GoodPathBounds.GoodPathAt p m α g c₃ C' := by
  have hm1 : 2073600 ≤ m + 1 := by
    have h2 : 2073600 ≤ m := by simpa [Threshold2.n₁] using hm
    omega
  have hN : 1 ≤ ParamsAdopted2.numStepsAdopted2 (m + 1) := by
    have := Submission.L10.three_le_numStepsAdopted2 (n := m + 1) (by omega); omega
  have hη0 := DriftStopped7.etaAdopted_nonneg (n := m + 1)
  have hr00 := DriftStopped7.r0Adopted_nonneg (n := m + 1)
  have hlt := GoodPathBounds.lt_a0C_of_mAt hm1 hc₃η
  have hmhalf := GoodPathBounds.half_le_mAt hm1 hc₃η
  rw [GoodPathBounds.mAt] at hmhalf
  have hδ1 : c₃ * DriftStopped6.etaAdopted (m + 1)
      < a0C (m + 1) - (DriftStopped6.r0Adopted (m + 1) + c₃ * DriftStopped6.etaAdopted (m + 1)) := by
    linarith
  have hA₀ := StateSupply.kSet_A0C (g := g) hraw
  have hA₀m := StateSupply.symMat_A0C (m + 1)
  have hE0 : (0 : ℝ) ≤ EaccAt (m + 1) c₃ := ChainErrBudget.epsAt_nonneg hm1 hc₃0 hc₃η
  have hbdabs : ChainErrBudget.StoppedErrBudget (qC α) (windowOfR α p m g) (A0C (m + 1))
      (ChainSetup.step (Submission.L10.cAdopted (m + 1))) (DriftStopped6.etaAdopted (m + 1))
      (DriftStopped6.r0Adopted (m + 1)) c₃ (ParamsAdopted2.numStepsAdopted2 (m + 1))
      (EaccAt (m + 1) c₃) :=
    ChainErrBudget.stoppedErrBudget_of_params (xs := fun y => xOf α y) hN hA₀ hA₀m
      hη0 hr00 hc₃0 hlt hδ1
  have hpre : ∀ ω, ∀ K, K < tau (qC α) (windowOfR α p m g) (A0C (m + 1))
        (ChainSetup.step (Submission.L10.cAdopted (m + 1))) (DriftStopped6.etaAdopted (m + 1))
        (DriftStopped6.r0Adopted (m + 1)) c₃ (ParamsAdopted2.numStepsAdopted2 (m + 1)) ω →
      ∑ k ∈ Finset.range K, ChainWiring.chainErr (qC α) (windowOfR α p m g) (A0C (m + 1))
        (ChainSetup.step (Submission.L10.cAdopted (m + 1))) k ω ≤ EaccAt (m + 1) c₃ :=
    fun _ω _K hK => sum_chainErr_le_c3 (xs := fun y => xOf α y) hA₀ hA₀m hη0 hr00 hc₃0 hlt hδ1 hK
  obtain ⟨ω, hω, hlog⟩ := goodPathAt_acc (q := qC α) (W := windowOfR α p m g)
    (A₀ := A0C (m + 1)) (r := 1) (ε := EaccAt (m + 1) c₃) (E := EaccAt (m + 1) c₃)
    hm1 one_pos hc₃0 hc₃η hA₀ (StateSupply.hq_of_raw (g := g) hraw)
    (StateSupply.hne_of_raw (g := g) hraw)
    hA₀m hE0 hbdabs hpre hS hcnt hLb hbudget
  exact ⟨1, 6 * 1 * 1 * Real.sqrt ((m + 1 : ℕ) : ℝ), ChainSetup.coord 0,
    ParamsAdopted2.numStepsAdopted2 (m + 1) - 1, ω, by omega, hω, hlog⟩

end GoodPathFree

/-! ## 6. The number at `c₃'' = n^{11/4}` -/

section Numbers

/-- **`E_acc ≤ 4/⁴√n` at the contact threshold `c₃'' = n³/⁴√n = n^{11/4}`.**
`DriftStopped6d.c3eta_le` gives `c₃''·η ≤ 2/⁴√n` and `DriftStopped6d.half_le_mAt''` gives
`m ≥ 1/2`.  The accumulated discretisation total is therefore **decreasing** in `n`, like
`n^{−1/4}`, against a drift gain of `4 log n`; charged `dim E` times it would be
`n(n+1)/2` larger. -/
theorem EaccAt_c3''_le {n : ℕ} (hn : 2073600 ≤ n) :
    EaccAt n (FinalDischarge2.c3Adopted'' n) ≤ 4 / Real.sqrt (Real.sqrt (n : ℝ)) := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hs : 0 < Real.sqrt (Real.sqrt (n : ℝ)) := Real.sqrt_pos.2 (Real.sqrt_pos.2 hn0)
  have hm := DriftStopped6d.half_le_mAt'' hn
  have hx := DriftStopped6d.c3eta_le hn
  have hmpos : 0 < GoodPathBounds.mAt n (FinalDischarge2.c3Adopted'' n) := by linarith
  have hrhs0 : (0 : ℝ) ≤ 4 / Real.sqrt (Real.sqrt (n : ℝ)) := by positivity
  rw [EaccAt_eq]
  have heq : FinalDischarge2.c3Adopted'' n
        * (DriftStopped6.etaAdopted n / GoodPathBounds.mAt n (FinalDischarge2.c3Adopted'' n))
      = (FinalDischarge2.c3Adopted'' n * DriftStopped6.etaAdopted n)
        / GoodPathBounds.mAt n (FinalDischarge2.c3Adopted'' n) := by
    ring
  rw [heq, div_le_iff₀ hmpos]
  have hhalf : 2 / Real.sqrt (Real.sqrt (n : ℝ))
      ≤ 4 / Real.sqrt (Real.sqrt (n : ℝ)) * GoodPathBounds.mAt n (FinalDischarge2.c3Adopted'' n) := by
    have h2 : 4 / Real.sqrt (Real.sqrt (n : ℝ)) * (1 / 2)
        ≤ 4 / Real.sqrt (Real.sqrt (n : ℝ)) * GoodPathBounds.mAt n (FinalDischarge2.c3Adopted'' n) :=
      mul_le_mul_of_nonneg_left hm hrhs0
    have h3 : 4 / Real.sqrt (Real.sqrt (n : ℝ)) * (1 / 2) = 2 / Real.sqrt (Real.sqrt (n : ℝ)) := by
      ring
    linarith
  linarith

/-- The freeze-budget term the *frozen* right-hand side charges, at the same `c₃''`:
`dim E · E_acc`, i.e. `n(n+1)/2` times the accumulated one. -/
theorem driftRHS_error_ratio (n : ℕ) (ε : ℝ) :
    (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) * ε
      = ((n : ℝ) * ((n : ℝ) + 1) / 2) * ε := by
  rw [ChainWiring.finrank_symSpace]
  have h : ((n * (n + 1) / 2 : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) + 1) / 2 := by
    have h2 : 2 ∣ n * (n + 1) := (Nat.even_mul_succ_self n).two_dvd
    obtain ⟨k, hk⟩ := h2
    rw [hk, Nat.mul_div_cancel_left _ (by norm_num)]
    have : ((n * (n + 1) : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) + 1) := by push_cast; ring
    rw [hk] at this
    push_cast at this ⊢
    linarith
  rw [h]

end Numbers

end Submission.L10.DriftAccumulated

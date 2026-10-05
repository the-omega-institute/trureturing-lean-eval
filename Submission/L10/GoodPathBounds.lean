import Submission.L10.StateSupply
import Submission.L10.ThetaTight
import Submission.L10.GoodPathLight

/-!
# Gate L-10 (`klartag_packing`) — the probabilistic half of `GoodPath`

Brief 82a.  Report 76 §3 names three things owed inside `StateSupply.GoodPath`: the free-dimension
total `hS`, the three failure bounds, and `hinterr`/`hG`.  This module supplies everything except
`hS` and the terminal-weight sum, which brief 82b derives from the light contact and which are
taken here as the two named inputs.

## The one structural correction

**Report 76 §3's note is wrong, and it changes the shape of the deliverable.**  It says the
`countGood` component of `wiredGood'` "may be taken at `c₃' = n³/4` while `stateGood`/
`stateBounds_wired'` stay at `n²`".  They cannot: `StateInvariant4.wiredGood'` (`:340`) has a
**single** `c₃`, which it passes to `countGood`, and `StateInvariant4.stateBounds_wired'` (`:379`)
reads that same `c₃` and reports `StateBounds` at `a₀ ∓ (r₀ + c₃·η)`.  The contact threshold and
the state's lower bound are one parameter.

So every theorem below carries `c₃` **free**, under the single hypothesis `c₃·η ≤ 1/4`, and the
adopted constants are generalised to it (`mAt`, `MAt`, `deltaAt`, `cqAt`; at `c₃ = c3Adopted n`
they are `DriftStopped6.mAdopted` etc. **definitionally**).  The report gives the measured verdict
on which `c₃` the count budget admits.

## What is here

* `mAt`–`cqAt` and their bounds — `DriftStopped7`'s numeric chain at a free contact threshold.
* `measurable_chainErr`, `measurable_stoppedErr`, `integrable_stoppedErr` — **`hinterr`**, from a
  two-sided freeze budget.  The tree bounds `chainErr` nowhere (`ChainWiring.lean:669` records the
  one-sided budget as still owed), so the two-sided form is the honest hypothesis and it discharges
  both `hinterr` and `drift_bound_stopped_maximal`'s `hbd`.
* `drift_bound_at` — `DriftInputsStopped.drift_bound_stopped_adopted` at a free `c₃`.
* `chainGood_failure`, `accGood_failure`, `countGood_failure_of_terminal_weight` — the three
  failure bounds.  The adopted `r₀ = 24√(log n/n)` is **exactly** `6·√(N·h)·√n`, so the GOE tail
  closes at `s = 1` with equality (`accGood_thr`), and the adopted `η = √(2hdn)` makes the per-step
  tail **exactly** `e^{−n}` (`step_tail_exponent`).
* `exists_mem_of_integral_le` — the existence step: Markov on `logDet − n·log m` against the
  failure budget.  Its `(B−L)/(b−L)` is report 80's existence slack in exact form.
* `goodPathAt` — a path of `wiredGood'` at a free `c₃` carrying eq. (68)'s bound.
* `goodPath_of_S` — the same at `c₃ = DriftStopped6.c3Adopted n`, i.e. literally
  `StateSupply.GoodPath p m α g C'`.
* `hS_of_intWeight` — **`hS`**, from `GoodPathLight.sum_free_ge_cut` at `Nfun := stoppedFreeDim`
  with the contact total rewritten by `ContactIntegrated.integrated_count_eq` into
  `(1/h)·∑_W intWeight` and bounded by the light contact.  `ContactIntegrated.sum_free_ge` does not
  apply (report 82b §2: the stopped free dimension is `0` after `τ`).
* `goodCut`, `goodPathCut`, `stateTriple_of_cut` — the same path with the contact count read at an
  index `K < N` rather than at `N`.  **This is what makes `c₃ = n²` reachable** (report
  82a-hinge): `wiredGood'` reads the count at the horizon, where the provable terminal weight is
  `n²` times larger than at the half-horizon.  `stateTriple_of_cut` is
  `DriftStopped8R.StateSupplyAdoptedR`'s conclusion directly, and at `c₃ = c3Adopted n` its lower
  bound `mAt n c₃` **is** `DriftStopped6.mAdopted n`.

`StateSupply.lean`, `ThetaTight.lean`, `TerminalCount.lean` and `DriftInputsStopped.lean` are
reported and are not edited; this module imports them.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Submission.L10.GoodPathBounds

open MeasureTheory Matrix Finset Module Submission.L10 Submission.L10.Increments
open Submission.L10.StoppedChain Submission.L10.DriftStopped Submission.L10.DriftStopped5
open Submission.L10.DriftInputsStopped Submission.L10.StateInvariant
open scoped NNReal RealInnerProductSpace

/-! ## 1. The adopted constants at a free contact threshold `c₃` -/

noncomputable def mAt (n : ℕ) (c₃ : ℝ) : ℝ :=
  a0C n - (DriftStopped6.r0Adopted n + c₃ * DriftStopped6.etaAdopted n)
noncomputable def MAt (n : ℕ) (c₃ : ℝ) : ℝ :=
  a0C n + (DriftStopped6.r0Adopted n + c₃ * DriftStopped6.etaAdopted n)
noncomputable def deltaAt (n : ℕ) (c₃ : ℝ) : ℝ := DriftStopped6.etaAdopted n / mAt n c₃
noncomputable def cqAt (n : ℕ) (c₃ : ℝ) : ℝ :=
  1 / (2 * MAt n c₃ ^ 2 * (1 + deltaAt n c₃) ^ 2)

section Consts
variable {n : ℕ} {c₃ : ℝ}

theorem half_le_mAt (hn : 2073600 ≤ n) (hc₃ : c₃ * DriftStopped6.etaAdopted n ≤ 1 / 4) :
    (1 : ℝ) / 2 ≤ mAt n c₃ := by
  have h1 := DriftStopped7.one_le_a0C (n := n) (by omega)
  have h2 := DriftStopped7.r0Adopted_le hn
  rw [mAt]; linarith

theorem one_le_MAt (hn : 2073600 ≤ n) (hc₃0 : 0 ≤ c₃) : (1 : ℝ) ≤ MAt n c₃ := by
  have h1 := DriftStopped7.one_le_a0C (n := n) (by omega)
  have h2 : 0 ≤ DriftStopped6.r0Adopted n := DriftStopped7.r0Adopted_nonneg
  have h3 : 0 ≤ c₃ * DriftStopped6.etaAdopted n :=
    mul_nonneg hc₃0 (DriftStopped7.etaAdopted_nonneg (n := n))
  rw [MAt]; linarith

theorem lt_a0C_of_mAt (hn : 2073600 ≤ n) (hc₃ : c₃ * DriftStopped6.etaAdopted n ≤ 1 / 4) :
    DriftStopped6.r0Adopted n + c₃ * DriftStopped6.etaAdopted n < a0C n := by
  have h := half_le_mAt hn hc₃; rw [mAt] at h; linarith

theorem deltaAt_nonneg (hn : 2073600 ≤ n) (hc₃ : c₃ * DriftStopped6.etaAdopted n ≤ 1 / 4) :
    0 ≤ deltaAt n c₃ := by
  have h := half_le_mAt hn hc₃
  rw [deltaAt]
  exact div_nonneg (DriftStopped7.etaAdopted_nonneg (n := n)) (by linarith)

theorem deltaAt_lt_one (hn : 2073600 ≤ n) (hc₃ : c₃ * DriftStopped6.etaAdopted n ≤ 1 / 4) :
    deltaAt n c₃ < 1 := by
  have hm := half_le_mAt hn hc₃
  have he := etaAdopted_le_quarter hn
  rw [deltaAt, div_lt_one (by linarith)]; linarith

theorem two_le_cqAt_den (hn : 2073600 ≤ n) (hc₃ : c₃ * DriftStopped6.etaAdopted n ≤ 1 / 4)
    (hc₃0 : 0 ≤ c₃) : (2 : ℝ) ≤ 2 * MAt n c₃ ^ 2 * (1 + deltaAt n c₃) ^ 2 := by
  have hM := one_le_MAt hn hc₃0
  have hd := deltaAt_nonneg hn hc₃
  have hM2 : (1 : ℝ) ≤ MAt n c₃ ^ 2 := by nlinarith
  have hd2 : (1 : ℝ) ≤ (1 + deltaAt n c₃) ^ 2 := by nlinarith
  nlinarith

theorem cqAt_nonneg (hn : 2073600 ≤ n) (hc₃ : c₃ * DriftStopped6.etaAdopted n ≤ 1 / 4)
    (hc₃0 : 0 ≤ c₃) : 0 ≤ cqAt n c₃ := by
  have h := two_le_cqAt_den hn hc₃ hc₃0
  rw [cqAt]; exact div_nonneg zero_le_one (by linarith)

end Consts


/-! ## 2. Ambient measurability of the chain's error -/

section Meas

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι] {Ω : Type*} [m0 : MeasurableSpace Ω]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

/-- The constant filtration, so the `ℱ`-relative lemmas of `DriftInputsStopped` give their ambient
forms with no second proof. -/
def constFil (m0 : MeasurableSpace Ω) : Filtration ℕ m0 where
  seq := fun _ => m0
  mono' := monotone_const
  le' := fun _ => le_rfl

theorem measurable_gaussStep (hξ : ∀ j, Measurable (ξ j)) (j : ℕ) :
    Measurable (StateInvariant.gaussStep q W A₀ ξ j) :=
  measurable_gaussStep_fil (constFil m0) (fun i => hξ i) j

theorem measurable_preState (hξ : ∀ j, Measurable (ξ j)) (k : ℕ) :
    Measurable (ChainWiring.preState q W A₀ ξ k) :=
  (Chain.measurable_chain_fst hξ k).add (measurable_gaussStep hξ k)

theorem measurable_logDet {α : Type*} [MeasurableSpace α] {f : α → EuclideanSpace ℝ (UT n)}
    (hf : Measurable f) : Measurable fun a => ChainWiring.logDet (f a) :=
  Real.measurable_log.comp ((DriftStopped6.continuous_symMat_det (n := n)).measurable.comp hf)

theorem measurable_chainErr (hξ : ∀ j, Measurable (ξ j)) (k : ℕ) :
    Measurable (ChainWiring.chainErr q W A₀ ξ k) := by
  have hpre := measurable_preState (q := q) (W := W) (A₀ := A₀) hξ k
  have hlift : Measurable fun ω => Chain.lift q W (ChainWiring.preState q W A₀ ξ k ω) :=
    (Chain.measurable_lift q W).comp hpre
  exact (measurable_logDet hlift).sub (measurable_logDet hpre)

theorem measurable_stoppedV_coord (hξ : ∀ j, Measurable (ξ j)) {η r₀ c₃ : ℝ} (N k : ℕ)
    (p : UT n) :
    Measurable fun ω => stoppedV q W A₀ ξ η r₀ c₃ N k ω p := by
  have hG : ∀ j, MeasurableSet[constFil m0 j] (stateGood q W A₀ ξ η r₀ c₃ j) := by
    intro j
    exact measurableSet_stateGood_fil (constFil m0) (fun i => hξ i) j
  exact (stronglyMeasurable_stoppedV_coord (constFil m0) (fun i => hξ i) hG N k p).measurable

theorem measurable_stoppedErr (hξ : ∀ j, Measurable (ξ j)) {η r₀ c₃ cq : ℝ} {N : ℕ}
    (hτ : Measurable (tau q W A₀ ξ η r₀ c₃ N)) (k : ℕ) :
    Measurable (stoppedErr q W A₀ ξ η r₀ c₃ cq N k) := by
  classical
  have hinner : Measurable fun ω => ⟪stoppedV q W A₀ ξ η r₀ c₃ N k ω, ξ k ω⟫ := by
    have hrep : (fun ω => ⟪stoppedV q W A₀ ξ η r₀ c₃ N k ω, ξ k ω⟫)
        = fun ω => ∑ p : UT n, stoppedV q W A₀ ξ η r₀ c₃ N k ω p * ξ k ω p := by
      funext ω; simp [PiLp.inner_apply, mul_comm]
    rw [hrep]
    exact Finset.measurable_sum _ fun p _ =>
      (measurable_stoppedV_coord hξ N k p).mul
        (((PiLp.continuous_apply 2 (fun _ : UT n => ℝ) p).measurable).comp (hξ k))
  have hmid : Measurable fun ω =>
      cq * ‖(Chain.freeSub q (Chain.chain q W A₀ ξ k ω).2).starProjection (ξ k ω)‖ ^ 2
        - ⟪stoppedV q W A₀ ξ η r₀ c₃ N k ω, ξ k ω⟫ :=
    (((measurable_gaussStep hξ k).norm.pow_const 2).const_mul cq).sub hinner
  have hs1 : MeasurableSet {ω | k + 1 ≤ tau q W A₀ ξ η r₀ c₃ N ω - 1} :=
    (hτ.sub_const 1) (measurableSet_Ici (a := k + 1))
  have hs2 : MeasurableSet {ω | k < tau q W A₀ ξ η r₀ c₃ N ω} :=
    hτ (measurableSet_Ioi (a := k))
  exact Measurable.ite hs1 (measurable_chainErr hξ k)
    (Measurable.ite hs2 hmid measurable_const)

end Meas

/-! ## 3. `hinterr`: integrability of the stopped error from a two-sided freeze budget -/

section Int

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}

theorem integrable_norm_step (c : ℝ) (k : ℕ) :
    Integrable (fun ω : ℕ → EuclideanSpace ℝ (UT n) => ‖ChainSetup.step c k ω‖)
      (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) := by
  have hdom : Integrable (fun ω : ℕ → EuclideanSpace ℝ (UT n) =>
      1 + ‖ChainSetup.step c k ω‖ ^ 2) (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) :=
    (integrable_const (1 : ℝ)).add (ChainSetup.integrable_norm_sq_step c k)
  refine Integrable.mono' hdom
    ((ChainSetup.measurable_step c k).norm.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  nlinarith [norm_nonneg (ChainSetup.step c k ω), sq_nonneg (‖ChainSetup.step c k ω‖ - 1)]

/-- **`hinterr`.**  The stopped error is dominated by the freeze budget plus a Gaussian second and
first moment: the branch before `τ − 1` is `chainErr`, bounded by `ε` in absolute value; the branch
at `τ − 1` is `DriftStopped2.stoppedErr_mid_le`'s integrand; after `τ` it is `0`. -/
theorem integrable_stoppedErr {a₀ η r₀ c₃ cq ε : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃) (hlt : r₀ + c₃ * η < a₀)
    (hcq : 0 ≤ cq) (hε : 0 ≤ ε) {cstep : ℝ}
    (hτ : Measurable (tau q W A₀ (ChainSetup.step cstep) η r₀ c₃ N))
    (hbd : ∀ ω k, |ChainWiring.chainErr q W A₀ (ChainSetup.step cstep) k ω| ≤ ε)
    (k : ℕ) :
    Integrable (stoppedErr q W A₀ (ChainSetup.step cstep) η r₀ c₃ cq N k)
      (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) := by
  classical
  set Cv : ℝ := Real.sqrt n / (a₀ - (r₀ + c₃ * η)) with hCv
  have hCv0 : 0 ≤ Cv := by
    have : 0 < a₀ - (r₀ + c₃ * η) := by linarith
    rw [hCv]; positivity
  have hdom : Integrable (fun ω : ℕ → EuclideanSpace ℝ (UT n) =>
      ε + cq * ‖ChainSetup.step cstep k ω‖ ^ 2 + Cv * ‖ChainSetup.step cstep k ω‖)
      (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) :=
    ((integrable_const ε).add ((ChainSetup.integrable_norm_sq_step cstep k).const_mul cq)).add
      ((integrable_norm_step cstep k).const_mul Cv)
  refine Integrable.mono' hdom
    (measurable_stoppedErr (fun j => ChainSetup.measurable_step cstep j) hτ k).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  have hnn : (0 : ℝ) ≤ ‖ChainSetup.step cstep k ω‖ := norm_nonneg _
  have hsq : (0 : ℝ) ≤ cq * ‖ChainSetup.step cstep k ω‖ ^ 2 := by positivity
  have hlin : (0 : ℝ) ≤ Cv * ‖ChainSetup.step cstep k ω‖ := mul_nonneg hCv0 hnn
  rw [stoppedErr]
  by_cases h1 : k + 1 ≤ tau q W A₀ (ChainSetup.step cstep) η r₀ c₃ N ω - 1
  · rw [ite_eq_left h1]
    have := hbd ω k
    rw [abs_le] at this ⊢
    constructor <;> linarith [this.1, this.2]
  · rw [ite_eq_right h1]
    by_cases h2 : k < tau q W A₀ (ChainSetup.step cstep) η r₀ c₃ N ω
    · rw [ite_eq_left h2]
      have hproj : ‖(Chain.freeSub q
          (Chain.chain q W A₀ (ChainSetup.step cstep) k ω).2).starProjection
          (ChainSetup.step cstep k ω)‖ ≤ ‖ChainSetup.step cstep k ω‖ :=
        Submodule.norm_starProjection_apply_le _ _
      have hp0 : (0 : ℝ) ≤ ‖(Chain.freeSub q
          (Chain.chain q W A₀ (ChainSetup.step cstep) k ω).2).starProjection
          (ChainSetup.step cstep k ω)‖ := norm_nonneg _
      have hq2 : ‖(Chain.freeSub q
          (Chain.chain q W A₀ (ChainSetup.step cstep) k ω).2).starProjection
          (ChainSetup.step cstep k ω)‖ ^ 2 ≤ ‖ChainSetup.step cstep k ω‖ ^ 2 := by nlinarith
      have hA : cq * ‖(Chain.freeSub q
          (Chain.chain q W A₀ (ChainSetup.step cstep) k ω).2).starProjection
          (ChainSetup.step cstep k ω)‖ ^ 2 ≤ cq * ‖ChainSetup.step cstep k ω‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hq2 hcq
      have hB : (0 : ℝ) ≤ cq * ‖(Chain.freeSub q
          (Chain.chain q W A₀ (ChainSetup.step cstep) k ω).2).starProjection
          (ChainSetup.step cstep k ω)‖ ^ 2 := by positivity
      have hV := DriftStopped2.norm_stoppedV_le (ξ := ChainSetup.step cstep) (N := N)
        hN hA₀ hq hne hA₀m hη hr₀ hc₃ hlt k ω
      have hinner : |⟪stoppedV q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω,
          ChainSetup.step cstep k ω⟫| ≤ Cv * ‖ChainSetup.step cstep k ω‖ :=
        le_trans (abs_real_inner_le_norm _ _) (mul_le_mul_of_nonneg_right hV hnn)
      rw [abs_le] at hinner ⊢
      constructor <;> linarith [hinner.1, hinner.2]
    · rw [ite_eq_right h2]
      rw [abs_zero]
      linarith

end Int


/-! ## 4. The drift bound at a free contact threshold -/

section Drift

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}

theorem drift_bound_at (hn : 2073600 ≤ n) {c₃ ε S : ℝ} {m : ℕ}
    (hc₃0 : 0 ≤ c₃) (hc₃η : c₃ * DriftStopped6.etaAdopted n ≤ 1 / 4)
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a0C n • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hinterr : ∀ k, Integrable
      (stoppedErr q W A₀ (ChainSetup.step (Submission.L10.cAdopted n))
        (DriftStopped6.etaAdopted n) (DriftStopped6.r0Adopted n) c₃ (cqAt n c₃)
        (ParamsAdopted2.numStepsAdopted2 n) k)
      (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))))
    (hS : S ≤ ∑ k ∈ Finset.range m, ∫ ω,
      DriftStopped6.stoppedFreeDim q W A₀ (ChainSetup.step (Submission.L10.cAdopted n))
        (DriftStopped6.etaAdopted n) (DriftStopped6.r0Adopted n) c₃
        (ParamsAdopted2.numStepsAdopted2 n) k ω
      ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))))
    (hε : 0 ≤ ε)
    (hbd : ∀ ω, ∀ k, k < m → ChainWiring.chainErr q W A₀
      (ChainSetup.step (Submission.L10.cAdopted n)) k ω ≤ ε) :
    ∫ ω, stoppedLogDet q W A₀ (ChainSetup.step (Submission.L10.cAdopted n))
        (DriftStopped6.etaAdopted n) (DriftStopped6.r0Adopted n) c₃
        (ParamsAdopted2.numStepsAdopted2 n) m ω
        ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))
      ≤ ∫ ω, stoppedLogDet q W A₀ (ChainSetup.step (Submission.L10.cAdopted n))
          (DriftStopped6.etaAdopted n) (DriftStopped6.r0Adopted n) c₃
          (ParamsAdopted2.numStepsAdopted2 n) 0 ω
          ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))
        - (cqAt n c₃ * Submission.L10.cAdopted n ^ 2) * S
        + ((finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) * ε
            + DriftStopped4.C₁ n (mAt n c₃) (cqAt n c₃) * (2 * Submission.L10.B_adopted n)) := by
  have hn3 : 3 ≤ n := by omega
  have hN : 1 ≤ ParamsAdopted2.numStepsAdopted2 n := by
    have := Submission.L10.three_le_numStepsAdopted2 hn3; omega
  have hG : ∀ k, MeasurableSet[ChainSetup.filtration (F := EuclideanSpace ℝ (UT n)) k]
      (stateGood q W A₀ (ChainSetup.step (Submission.L10.cAdopted n))
        (DriftStopped6.etaAdopted n) (DriftStopped6.r0Adopted n) c₃ k) :=
    fun k => measurableSet_stateGood_step _ _ _ _ k
  have hlt := lt_a0C_of_mAt hn hc₃η
  have hcq0 := cqAt_nonneg hn hc₃η hc₃0
  have hκ : (0 : ℝ) ≤ cqAt n c₃ * Submission.L10.cAdopted n ^ 2 := by positivity
  have hrec := driftInputs_stopped (q := q) (W := W) (A₀ := A₀) (m := m) hN hA₀ hq hne hA₀m
    (DriftStopped7.etaAdopted_nonneg (n := n)) (DriftStopped7.r0Adopted_nonneg (n := n)) hc₃0 hlt
    (le_of_eq (by rw [deltaAt, mAt])) (deltaAt_nonneg hn hc₃η) (deltaAt_lt_one hn hc₃η)
    (by rw [cqAt, MAt]) hinterr
  exact DriftStopped6.drift_bound_stopped_maximal
    (ℱ := ChainSetup.filtration (F := EuclideanSpace ℝ (UT n)))
    hrec hG hκ hS hN hcq0 hA₀ hq hne hA₀m
    (DriftStopped7.etaAdopted_nonneg (n := n)) (DriftStopped7.r0Adopted_nonneg (n := n))
    hc₃0 hlt hε hbd (fun k _ => hinterr k)
    (Submission.L10.maximalAtAdopted_adopted hn3)
    (Submission.L10.integrableAtIndex_adopted hn3)

end Drift


/-! ## 5. The three failure bounds -/

section Fail

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}

theorem etaAdopted_pos (hn : 3 ≤ n) : 0 < DriftStopped6.etaAdopted n := by
  have h1 : (0 : ℝ) < ParamsAdopted2.stepSizeAdopted2 n := Submission.L10.stepSizeAdopted2_pos hn
  have h2 : (0 : ℝ) < (Fintype.card (UT n) : ℝ) := by
    exact_mod_cast Submission.L10.card_UT_pos hn
  have h3 : (0 : ℝ) < (n : ℝ) := by
    have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  rw [DriftStopped6.etaAdopted]
  exact Real.sqrt_pos.2 (by positivity)

/-- `v = c² = h` at the adopted step scale. -/
theorem coe_v_adopted (hn : 3 ≤ n) :
    ((Real.toNNReal (Submission.L10.cAdopted n ^ 2) : ℝ≥0) : ℝ)
      = ParamsAdopted2.stepSizeAdopted2 n := by
  rw [Real.coe_toNNReal _ (sq_nonneg _), Submission.L10.cAdopted,
    Real.sq_sqrt (Submission.L10.stepSizeAdopted2_pos hn).le]

/-- **The per-step tail is exactly `e^{−n}`** — the adopted `η = √(2hdn)` is chosen for it. -/
theorem step_tail_exponent (hn : 3 ≤ n) :
    -(DriftStopped6.etaAdopted n ^ 2 / (Fintype.card (UT n) : ℝ))
        / (2 * ((Real.toNNReal (Submission.L10.cAdopted n ^ 2) : ℝ≥0) : ℝ)) = -(n : ℝ) := by
  have hh : (0 : ℝ) < ParamsAdopted2.stepSizeAdopted2 n := Submission.L10.stepSizeAdopted2_pos hn
  have hd : (0 : ℝ) < (Fintype.card (UT n) : ℝ) := by
    exact_mod_cast Submission.L10.card_UT_pos hn
  have hsq : DriftStopped6.etaAdopted n ^ 2
      = 2 * ParamsAdopted2.stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ) * (n : ℝ) := by
    rw [DriftStopped6.etaAdopted, Real.sq_sqrt (by positivity)]
  rw [hsq, coe_v_adopted hn]
  field_simp

/-- **The `chainGood` failure bound** at `s = 1`, with `Wacc = coord 0` (the `goodEventUT`
component of `chainGood` is never read downstream — report 49 §1 — so any standard Gaussian
serves). -/
theorem chainGood_failure (hn : 3 ≤ n) {r : ℝ} (hr : 0 < r) :
    (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))).real
        (StepGlue.chainGood r (ChainSetup.coord 0)
          (ChainSetup.step (Submission.L10.cAdopted n)) (6 * r * 1 * Real.sqrt n)
          (ParamsAdopted2.numStepsAdopted2 n) (DriftStopped6.etaAdopted n))ᶜ
      ≤ (33 * (n : ℝ) ^ 9 * Real.log n + 4) * Real.exp (-(n : ℝ)) := by
  have hbase := StepGlue.measureReal_compl_chainGood_le
    (P := ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) (n := n) hr
    (ChainSetup.measurable_coord 0) (ChainSetup.map_coord 0)
    (ξ := ChainSetup.step (Submission.L10.cAdopted n))
    (v := Real.toNNReal (Submission.L10.cAdopted n ^ 2))
    (fun k p => ChainSetup.step_coord_law (Submission.L10.cAdopted n) k p)
    (etaAdopted_pos hn) (ParamsAdopted2.numStepsAdopted2 n) 1 le_rfl
  refine StateInvariant2.failure_le2 hn ?_
  refine le_trans hbase (le_of_eq ?_)
  rw [step_tail_exponent hn]
  norm_num

/-- **The `accGood` failure bound.**  The adopted `r₀ = 24√(log n/n)` is exactly
`6·√(N·h)·√n`, so the GOE tail closes at `s = 1` with equality. -/
theorem accGood_thr (hn : 3 ≤ n) :
    6 * (Real.sqrt (ParamsAdopted2.numStepsAdopted2 n) * Submission.L10.cAdopted n) * 1
        * Real.sqrt n ≤ DriftStopped6.r0Adopted n := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hlog : (0 : ℝ) ≤ Real.log n := le_trans (by norm_num) (ChainDrift.log_pos_of_three hn)
  have hNh := ParamsAdopted2.numStepsAdopted2_mul_stepSizeAdopted2 hn
  have hprod : Real.sqrt (ParamsAdopted2.numStepsAdopted2 n) * Submission.L10.cAdopted n
      = Real.sqrt (ChainDrift.horizon n) := by
    rw [Submission.L10.cAdopted, ← Real.sqrt_mul (by positivity), hNh]
  have hhor : Real.sqrt (ChainDrift.horizon n) = 4 * Real.sqrt (Real.log n) / (n : ℝ) := by
    rw [ChainDrift.horizon, Real.sqrt_div' _ (by positivity), show (16 : ℝ) * Real.log n
      = 4 ^ 2 * Real.log n by norm_num, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by norm_num), show ((n : ℝ) ^ 2) = (n : ℝ) ^ 2 from rfl,
      Real.sqrt_sq hn0.le]
  have hr0 : DriftStopped6.r0Adopted n = 24 * (Real.sqrt (Real.log n) / Real.sqrt n) := by
    rw [DriftStopped6.r0Adopted, Real.sqrt_div' _ hn0.le]
  rw [hprod, hhor, hr0]
  have hsq : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt hn0.le
  have hspos : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.2 hn0
  rw [le_iff_eq_or_lt]
  left
  field_simp
  nlinarith [hsq, hspos, Real.sqrt_nonneg (Real.log n)]

theorem accGood_failure (hn : 3 ≤ n) :
    (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))).real
        (accGood q W A₀ (ChainSetup.step (Submission.L10.cAdopted n))
          (ParamsAdopted2.numStepsAdopted2 n) (DriftStopped6.r0Adopted n))ᶜ
      ≤ ((ParamsAdopted2.numStepsAdopted2 n : ℕ) : ℝ)
          * (2 * (4 * Real.exp (-(1 ^ 2 * (n : ℝ))))) :=
  StateInvariant4.measureReal_compl_accGood_le' (Submission.L10.cAdopted_pos hn)
    DriftStopped7.r0Adopted_nonneg le_rfl
    (fun k => ChainSetup.measurable_step (Submission.L10.cAdopted n) k)
    (ChainSetup.iIndepFun_step (Submission.L10.cAdopted n))
    (fun j => ChainSetup.map_step (Submission.L10.cAdopted n) j) (accGood_thr hn)

end Fail


/-! ## 6. The stopped log-determinant at `0`, and its uniform lower bound -/

section Bounds

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι] {Ω : Type*} [m0 : MeasurableSpace Ω]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

theorem stoppedLogDet_zero {η r₀ c₃ : ℝ} {N : ℕ} (ω : Ω) :
    stoppedLogDet q W A₀ ξ η r₀ c₃ N 0 ω = ChainWiring.logDet A₀ := by
  rw [stoppedLogDet, stoppedState, Nat.zero_min, Chain.chain_zero]

/-- **The uniform lower bound on the stopped log-determinant**, from
`StoppedChain.stateBounds_stopped` (which holds everywhere) and
`DriftStopped6.det_bounds_of_stateBounds`.  This is the `L` the existence step's Markov step
shifts by. -/
theorem stoppedLogDet_ge {η a₀ r₀ c₃ : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃) (hlt : r₀ + c₃ * η < a₀) (k : ℕ) (ω : Ω) :
    (n : ℝ) * Real.log (a₀ - (r₀ + c₃ * η)) ≤ stoppedLogDet q W A₀ ξ η r₀ c₃ N k ω := by
  have hm : (0 : ℝ) < a₀ - (r₀ + c₃ * η) := by linarith
  have hSB := stateBounds_stopped (ξ := ξ) (N := N) hN hA₀ hq hne hA₀m hη hr₀ hc₃ hlt k ω
  obtain ⟨h1, _⟩ := DriftStopped6.det_bounds_of_stateBounds hSB
  have hpos : 0 < (symMat (stoppedState q W A₀ ξ η r₀ c₃ N k ω)).det := hSB.posDef.det_pos
  rw [stoppedLogDet, ChainWiring.logDet, ← Real.log_pow]
  exact Real.log_le_log (pow_pos hm n) h1

end Bounds

/-! ## 7. Expectation to existence, with a lower bound and a failure budget -/

section Existence

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The two-event pigeonhole**, self-contained: `DriftStopped6.exists_mem_inter_of_one_lt` is
stated inside a section whose chain variables are not determined by its statement, so applying it
leaves `IsProbabilityMeasure` stuck on a metavariable. -/
theorem exists_mem_inter_of_one_lt' {G S : Set Ω} (hS : MeasurableSet S)
    (h : 1 < P.real G + P.real S) : ∃ ω, ω ∈ G ∧ ω ∈ S := by
  by_contra hcon
  have hcon : ∀ ω, ω ∈ G → ω ∉ S := fun ω hg hs => hcon ⟨ω, hg, hs⟩
  have hdisj : AEDisjoint P G S := by
    have hempty : G ∩ S = (∅ : Set Ω) := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      exact hcon ω
    rw [AEDisjoint, hempty]
    simp
  have hadd : P.real (G ∪ S) = P.real G + P.real S :=
    measureReal_union₀ hS.nullMeasurableSet hdisj (measure_ne_top P G) (measure_ne_top P S)
  have hle : P.real (G ∪ S) ≤ 1 := measureReal_le_one
  linarith

/-- **The existence step.**  Markov on `f − L` gives `P(f ≥ b) ≤ (B−L)/(b−L)`; the good event
fails with probability at most `pbad`; if the two budgets sum below `1` the events meet.  The
`(B−L)/(b−L)` is report 80's existence slack in exact form. -/
theorem exists_mem_of_integral_le {f : Ω → ℝ} (hfm : Measurable f) (hf : Integrable f P)
    {L B b pbad : ℝ} (hL : ∀ ω, L ≤ f ω) (hB : ∫ ω, f ω ∂P ≤ B)
    {S : Set Ω} (hS : MeasurableSet S) (hbad : P.real Sᶜ ≤ pbad) (hLb : L < b)
    (hbudget : (B - L) / (b - L) + pbad < 1) :
    ∃ ω, f ω ≤ b ∧ ω ∈ S := by
  classical
  have hg : Integrable (fun ω => f ω - L) P := hf.sub (integrable_const L)
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := P) (f := fun ω => f ω - L)
    (Filter.Eventually.of_forall fun ω => sub_nonneg.2 (hL ω)) hg (b - L)
  have hint : ∫ ω, (f ω - L) ∂P = (∫ ω, f ω ∂P) - L := by
    rw [integral_sub hf (integrable_const L), integral_const]
    simp
  rw [hint] at hmk
  have hset : {ω | b - L ≤ f ω - L} = {ω | b ≤ f ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    constructor <;> intro h <;> linarith
  rw [hset] at hmk
  have hmeas : MeasurableSet {ω | f ω ≤ b} := measurableSet_le hfm measurable_const
  have hsub : {ω | f ω ≤ b}ᶜ ⊆ {ω | b ≤ f ω} := by
    intro ω hω
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hω ⊢
    linarith
  have hle : P.real {ω | f ω ≤ b}ᶜ ≤ P.real {ω | b ≤ f ω} :=
    measureReal_mono hsub (measure_ne_top P _)
  have hmark : P.real {ω | b ≤ f ω} ≤ (B - L) / (b - L) := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith [hmk, hB]
  have hG : P.real {ω | f ω ≤ b} + P.real {ω | f ω ≤ b}ᶜ = 1 := by
    rw [measureReal_add_measureReal_compl hmeas]
    simp
  have hSsum : P.real S + P.real Sᶜ = 1 := by
    rw [measureReal_add_measureReal_compl hS]
    simp
  refine exists_mem_inter_of_one_lt' (P := P) (G := {ω | f ω ≤ b}) hS ?_
  linarith

end Existence


/-! ## 8. Measurability of the good event -/

section MeasSets

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι] {Ω : Type*} [m0 : MeasurableSpace Ω]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

theorem measurable_gaussSum (hξ : ∀ j, Measurable (ξ j)) (k : ℕ) :
    Measurable (StateInvariant.gaussSum q W A₀ ξ k) :=
  measurable_gaussSum_fil (constFil m0) (fun i => hξ i) k

/-- The operator norm of `r • symMat` is measurable — `Increments.measurable_opNorm_mkMat`
through `Increments.smul_symMat_eq_mkMat`. -/
theorem measurable_opNorm_smul_symMat {α : Type*} [MeasurableSpace α] (r : ℝ)
    {f : α → EuclideanSpace ℝ (UT n)} (hf : Measurable f) :
    Measurable fun a => ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (r • symMat (f a))‖ := by
  have hmk : (fun a => ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (r • symMat (f a))‖)
      = fun a => ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (mkMat (coordVec r (f a)))‖ := by
    funext a; rw [smul_symMat_eq_mkMat r (f a)]
  rw [hmk]
  exact (measurable_opNorm_mkMat (n := n)).comp ((measurable_coordVec (n := n) r).comp hf)

theorem measurable_opNorm_symMat {α : Type*} [MeasurableSpace α]
    {f : α → EuclideanSpace ℝ (UT n)} (hf : Measurable f) :
    Measurable fun a => ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat (f a))‖ := by
  have h := measurable_opNorm_smul_symMat (1 : ℝ) hf
  simpa using h

theorem measurableSet_goodEventUT {Wacc : Ω → EuclideanSpace ℝ (UT n)} (hW : Measurable Wacc)
    (r thr : ℝ) : MeasurableSet (StepInputs.goodEventUT r Wacc thr) :=
  measurableSet_le (measurable_opNorm_smul_symMat r hW) measurable_const

theorem measurableSet_stepGood (hξ : ∀ j, Measurable (ξ j)) (N : ℕ) (η : ℝ) :
    MeasurableSet (StepInputs2.stepGood ξ N η) := by
  have hrep : StepInputs2.stepGood ξ N η = ⋂ k ∈ {k : ℕ | k < N}, {ω | ‖ξ k ω‖ ≤ η} := by
    ext ω
    simp only [StepInputs2.stepGood, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [hrep]
  exact MeasurableSet.biInter (Set.to_countable _)
    fun k _ => measurableSet_le (hξ k).norm measurable_const

theorem measurableSet_accGood (hξ : ∀ j, Measurable (ξ j)) (N : ℕ) (r₀ : ℝ) :
    MeasurableSet (StateInvariant.accGood q W A₀ ξ N r₀) := by
  have hrep : StateInvariant.accGood q W A₀ ξ N r₀
      = ⋂ k ∈ {k : ℕ | k < N},
        {ω | ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
          (symMat (StateInvariant.gaussSum q W A₀ ξ k ω))‖ ≤ r₀} := by
    ext ω
    simp only [StateInvariant.accGood, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [hrep]
  exact MeasurableSet.biInter (Set.to_countable _)
    fun k _ => measurableSet_le (measurable_opNorm_symMat (measurable_gaussSum hξ k))
      measurable_const

theorem measurableSet_countGood (hξ : ∀ j, Measurable (ξ j)) (N : ℕ) (c₃ : ℝ) :
    MeasurableSet (StateInvariant4.countGood q W A₀ ξ N c₃) :=
  measurableSet_le (StateInvariant4.measurable_card_chain hξ N) measurable_const

theorem measurableSet_wiredGood' (hξ : ∀ j, Measurable (ξ j))
    {Wacc : Ω → EuclideanSpace ℝ (UT n)} (hW : Measurable Wacc) (r thr : ℝ) (N : ℕ)
    (η r₀ c₃ : ℝ) :
    MeasurableSet (StateInvariant4.wiredGood' r Wacc ξ thr N η q W A₀ r₀ c₃) :=
  ((measurableSet_goodEventUT hW r thr).inter (measurableSet_stepGood hξ N η)).inter
    (measurableSet_accGood hξ N r₀) |>.inter (measurableSet_countGood hξ N c₃)

end MeasSets

/-! ## 9. `countGood`'s failure bound, and the assembly -/

section Assembly

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}

/-- **The count event's failure bound** from the terminal weight, in the shape brief 82b's second
input produces (`TerminalCount.countGood_of_terminal_weight`). -/
theorem countGood_failure {c₃ θT : ℝ} (hc₃ : 0 < c₃) (weight : ι → ℝ)
    (htail : ∀ i ∈ W, (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))).real
      {ω | i ∈ (Chain.chain q W A₀ (ChainSetup.step (Submission.L10.cAdopted n))
        (ParamsAdopted2.numStepsAdopted2 n) ω).2} ≤ 2 * weight i + 0)
    (hθ : ∑ i ∈ W, weight i ≤ θT) :
    (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))).real
        (StateInvariant4.countGood q W A₀ (ChainSetup.step (Submission.L10.cAdopted n))
          (ParamsAdopted2.numStepsAdopted2 n) c₃)ᶜ
      ≤ (2 * θT + 0) / c₃ :=
  TerminalCount.countGood_of_terminal_weight
    (fun k => ChainSetup.measurable_step (Submission.L10.cAdopted n) k) hc₃ weight htail hθ

/-- The drift bound's right-hand side, named. -/
noncomputable def driftRHS (n : ℕ) (A₀ : EuclideanSpace ℝ (UT n)) (c₃ ε S : ℝ) : ℝ :=
  ChainWiring.logDet A₀ - (cqAt n c₃ * Submission.L10.cAdopted n ^ 2) * S
    + ((finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) * ε
        + DriftStopped4.C₁ n (mAt n c₃) (cqAt n c₃) * (2 * Submission.L10.B_adopted n))

/-- The uniform lower bound on the stopped log-determinant, named. -/
noncomputable def logDetLow (n : ℕ) (c₃ : ℝ) : ℝ := (n : ℝ) * Real.log (mAt n c₃)

/-- The three failure probabilities, summed. -/
noncomputable def failTotal (n : ℕ) (pcnt : ℝ) : ℝ :=
  (33 * (n : ℝ) ^ 9 * Real.log n + 4) * Real.exp (-(n : ℝ))
    + ((ParamsAdopted2.numStepsAdopted2 n : ℕ) : ℝ)
        * (2 * (4 * Real.exp (-((1 : ℝ) ^ 2 * (n : ℝ))))) + pcnt

/-- **A path of `wiredGood'` carrying eq. (68)'s bound, at a free contact threshold.**  This is
`StateSupply.GoodPath`'s content with `c₃` left open; §10 instantiates it. -/
theorem goodPathAt (hn : 2073600 ≤ n) {c₃ ε S b pcnt r : ℝ} (hr : 0 < r)
    (hc₃0 : 0 ≤ c₃) (hc₃η : c₃ * DriftStopped6.etaAdopted n ≤ 1 / 4)
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a0C n • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hε : 0 ≤ ε)
    (hbdabs : ∀ ω, ∀ k, |ChainWiring.chainErr q W A₀
      (ChainSetup.step (Submission.L10.cAdopted n)) k ω| ≤ ε)
    (hS : S ≤ ∑ k ∈ Finset.range (ParamsAdopted2.numStepsAdopted2 n - 1), ∫ ω,
      DriftStopped6.stoppedFreeDim q W A₀ (ChainSetup.step (Submission.L10.cAdopted n))
        (DriftStopped6.etaAdopted n) (DriftStopped6.r0Adopted n) c₃
        (ParamsAdopted2.numStepsAdopted2 n) k ω
      ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))))
    (hcnt : (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))).real
        (StateInvariant4.countGood q W A₀ (ChainSetup.step (Submission.L10.cAdopted n))
          (ParamsAdopted2.numStepsAdopted2 n) c₃)ᶜ ≤ pcnt)
    (hLb : logDetLow n c₃ < b)
    (hbudget : (driftRHS n A₀ c₃ ε S - logDetLow n c₃) / (b - logDetLow n c₃)
      + failTotal n pcnt < 1) :
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
    measurable_tau (ChainSetup.filtration (F := EuclideanSpace ℝ (UT n))) hG _
  have hlt := lt_a0C_of_mAt hn hc₃η
  have hinterr := fun k => integrable_stoppedErr (q := q) (W := W) (A₀ := A₀)
    (cq := cqAt n c₃) (ε := ε) hN hA₀ hq hne hA₀m
    (DriftStopped7.etaAdopted_nonneg (n := n)) (DriftStopped7.r0Adopted_nonneg (n := n))
    hc₃0 hlt (cqAt_nonneg hn hc₃η hc₃0) hε hτ hbdabs k
  -- the drift bound
  have hdrift := drift_bound_at (q := q) (W := W) (A₀ := A₀) (m := ParamsAdopted2.numStepsAdopted2 n - 1)
    hn hc₃0 hc₃η hA₀ hq hne hA₀m hinterr hS hε
    (fun ω k _ => le_trans (le_abs_self _) (hbdabs ω k))
  have hzero : ∫ ω, stoppedLogDet q W A₀ (ChainSetup.step (Submission.L10.cAdopted n))
        (DriftStopped6.etaAdopted n) (DriftStopped6.r0Adopted n) c₃
        (ParamsAdopted2.numStepsAdopted2 n) 0 ω
        ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))
      = ChainWiring.logDet A₀ := by
    simp only [stoppedLogDet_zero]
    simp
  rw [hzero] at hdrift
  -- the failure budget
  have hfail : (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))).real
      (StateInvariant4.wiredGood' r (ChainSetup.coord 0)
        (ChainSetup.step (Submission.L10.cAdopted n)) (6 * r * 1 * Real.sqrt n)
        (ParamsAdopted2.numStepsAdopted2 n) (DriftStopped6.etaAdopted n) q W A₀
        (DriftStopped6.r0Adopted n) c₃)ᶜ ≤ failTotal n pcnt := by
    refine le_trans (StateInvariant4.measureReal_compl_wiredGood'_le _ _ _ _ _ _ _) ?_
    rw [failTotal]
    have h1 := chainGood_failure (n := n) hn3 hr
    have h2 := accGood_failure (q := q) (W := W) (A₀ := A₀) hn3
    linarith [hcnt]
  refine DriftStopped6.exists_logDet_le_on_wiredGood' (le_refl _) ?_
  refine exists_mem_of_integral_le
    (DriftStopped6.measurable_stoppedLogDet hξm hτ _)
    (DriftStopped6.integrable_stoppedLogDet hN hξm hτ hA₀ hq hne hA₀m
      (DriftStopped7.etaAdopted_nonneg (n := n)) (DriftStopped7.r0Adopted_nonneg (n := n))
      hc₃0 hlt _)
    (L := logDetLow n c₃) (B := driftRHS n A₀ c₃ ε S)
    (fun ω => stoppedLogDet_ge hN hA₀ hq hne hA₀m
      (DriftStopped7.etaAdopted_nonneg (n := n)) (DriftStopped7.r0Adopted_nonneg (n := n))
      hc₃0 hlt _ ω)
    hdrift
    (measurableSet_wiredGood' hξm (ChainSetup.measurable_coord 0) _ _ _ _ _ _)
    hfail hLb hbudget

end Assembly

/-! ## 10. `StateSupply.GoodPath`, at the adopted contact threshold -/

section GoodPath

open Submission.L10.ConstructionA Submission.L10.Tiling Submission.L10.PaddedLawSetupR
open Submission.L10.RawDataInst2R Submission.L10.RawDataInst2 Submission.L10.DriftStopped8R

variable {p m : ℕ} {α R C' : ℝ} {g : Fin (m + 1) → ZMod p}

/-- **`StateSupply.GoodPath` from the two named inputs.**  `c₃` is `DriftStopped6.c3Adopted (m+1)`
because `StateSupply.GoodPath` (`:98`) pins it there; `DriftStopped7.c3_mul_eta_le` is the
`c₃·η ≤ 1/4` §1 needs.  The two inputs brief 82b owes are `hS` and `hcnt` (through
`countGood_failure`); `hbdabs` is the two-sided freeze budget of §3. -/
theorem goodPath_of_S (hm : Threshold2.n₁ ≤ m)
    (hraw : RawDataR p (m + 1) α R (qC α) (shellR α (m + 1)) (A0C (m + 1)))
    {ε S pcnt : ℝ} (hε : 0 ≤ ε)
    (hbdabs : ∀ ω, ∀ k, |ChainWiring.chainErr (qC α) (windowOfR α p m g) (A0C (m + 1))
      (ChainSetup.step (Submission.L10.cAdopted (m + 1))) k ω| ≤ ε)
    (hS : S ≤ ∑ k ∈ Finset.range (ParamsAdopted2.numStepsAdopted2 (m + 1) - 1), ∫ ω,
      DriftStopped6.stoppedFreeDim (qC α) (windowOfR α p m g) (A0C (m + 1))
        (ChainSetup.step (Submission.L10.cAdopted (m + 1)))
        (DriftStopped6.etaAdopted (m + 1)) (DriftStopped6.r0Adopted (m + 1))
        (DriftStopped6.c3Adopted (m + 1)) (ParamsAdopted2.numStepsAdopted2 (m + 1)) k ω
      ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT (m + 1)))))
    (hcnt : (ChainSetup.gaussPath (EuclideanSpace ℝ (UT (m + 1)))).real
        (StateInvariant4.countGood (qC α) (windowOfR α p m g) (A0C (m + 1))
          (ChainSetup.step (Submission.L10.cAdopted (m + 1)))
          (ParamsAdopted2.numStepsAdopted2 (m + 1))
          (DriftStopped6.c3Adopted (m + 1)))ᶜ ≤ pcnt)
    (hLb : logDetLow (m + 1) (DriftStopped6.c3Adopted (m + 1))
      < C' - 4 * Real.log ((m + 1 : ℕ) : ℝ))
    (hbudget : (driftRHS (m + 1) (A0C (m + 1)) (DriftStopped6.c3Adopted (m + 1)) ε S
          - logDetLow (m + 1) (DriftStopped6.c3Adopted (m + 1)))
        / ((C' - 4 * Real.log ((m + 1 : ℕ) : ℝ))
          - logDetLow (m + 1) (DriftStopped6.c3Adopted (m + 1)))
      + failTotal (m + 1) pcnt < 1) :
    StateSupply.GoodPath p m α g C' := by
  have hm1 : 2073600 ≤ m + 1 := by
    have h2 : 2073600 ≤ m := by simpa [Threshold2.n₁] using hm
    omega
  have hN : 1 ≤ ParamsAdopted2.numStepsAdopted2 (m + 1) := by
    have := Submission.L10.three_le_numStepsAdopted2 (n := m + 1) (by omega); omega
  obtain ⟨ω, hω, hlog⟩ := goodPathAt (q := qC α) (W := windowOfR α p m g)
    (A₀ := A0C (m + 1)) (r := 1) hm1 one_pos
    (by rw [DriftStopped6.c3Adopted]; positivity)
    (DriftStopped7.c3_mul_eta_le hm1)
    (StateSupply.kSet_A0C hraw) (StateSupply.hq_of_raw hraw) (StateSupply.hne_of_raw hraw)
    (StateSupply.symMat_A0C (m + 1)) hε hbdabs hS hcnt hLb hbudget
  exact ⟨1, 6 * 1 * 1 * Real.sqrt ((m + 1 : ℕ) : ℝ), ChainSetup.coord 0,
    ParamsAdopted2.numStepsAdopted2 (m + 1) - 1, ω, by omega, hω, hlog⟩

end GoodPath

/-! ## 11. The same with the contact threshold free — the hand-off shape -/

section GoodPathFree

open Submission.L10.ConstructionA Submission.L10.Tiling Submission.L10.PaddedLawSetupR
open Submission.L10.RawDataInst2R Submission.L10.RawDataInst2 Submission.L10.DriftStopped8R

variable {p m : ℕ} {α C' : ℝ} {g : Fin (m + 1) → ZMod p}

/-- **`StateSupply.GoodPath` with `c₃` free.**  `StateSupply.GoodPath p m α g C'` is
`GoodPathAt p m α g (DriftStopped6.c3Adopted (m+1)) C'` definitionally; a successor that moves the
contact threshold re-cuts `StateSupplyAdoptedR`'s `mLow` to `mAt (m+1) c₃` and consumes this. -/
def GoodPathAt (p m : ℕ) (α : ℝ) (g : Fin (m + 1) → ZMod p) (c₃ C' : ℝ) : Prop :=
  ∃ (r thr : ℝ)
    (Wacc : (ℕ → EuclideanSpace ℝ (UT (m + 1))) → EuclideanSpace ℝ (UT (m + 1)))
    (K : ℕ) (ω : ℕ → EuclideanSpace ℝ (UT (m + 1))),
    K < ParamsAdopted2.numStepsAdopted2 (m + 1) ∧
    ω ∈ StateInvariant4.wiredGood' r Wacc
        (ChainSetup.step (Submission.L10.cAdopted (m + 1))) thr
        (ParamsAdopted2.numStepsAdopted2 (m + 1)) (DriftStopped6.etaAdopted (m + 1))
        (qC α) (windowOfR α p m g) (A0C (m + 1))
        (DriftStopped6.r0Adopted (m + 1)) c₃ ∧
    ChainWiring.logDet (Chain.chain (qC α) (windowOfR α p m g) (A0C (m + 1))
        (ChainSetup.step (Submission.L10.cAdopted (m + 1))) K ω).1
      ≤ C' - 4 * Real.log ((m + 1 : ℕ) : ℝ)

theorem goodPath_eq_goodPathAt :
    StateSupply.GoodPath p m α g C'
      = GoodPathAt p m α g (DriftStopped6.c3Adopted (m + 1)) C' := rfl

/-- **The deliverable at a free contact threshold.**  Identical to `goodPath_of_S` except that
`c₃` is a parameter with `0 ≤ c₃` and `c₃·η ≤ 1/4`; the report measures which `c₃` the count
budget admits. -/
theorem goodPathAt_of_S (hm : Threshold2.n₁ ≤ m) {R : ℝ}
    (hraw : RawDataR p (m + 1) α R (qC α) (shellR α (m + 1)) (A0C (m + 1)))
    {c₃ ε S pcnt : ℝ} (hc₃0 : 0 ≤ c₃)
    (hc₃η : c₃ * DriftStopped6.etaAdopted (m + 1) ≤ 1 / 4) (hε : 0 ≤ ε)
    (hbdabs : ∀ ω, ∀ k, |ChainWiring.chainErr (qC α) (windowOfR α p m g) (A0C (m + 1))
      (ChainSetup.step (Submission.L10.cAdopted (m + 1))) k ω| ≤ ε)
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
    (hLb : logDetLow (m + 1) c₃ < C' - 4 * Real.log ((m + 1 : ℕ) : ℝ))
    (hbudget : (driftRHS (m + 1) (A0C (m + 1)) c₃ ε S - logDetLow (m + 1) c₃)
        / ((C' - 4 * Real.log ((m + 1 : ℕ) : ℝ)) - logDetLow (m + 1) c₃)
      + failTotal (m + 1) pcnt < 1) :
    GoodPathAt p m α g c₃ C' := by
  have hm1 : 2073600 ≤ m + 1 := by
    have h2 : 2073600 ≤ m := by simpa [Threshold2.n₁] using hm
    omega
  have hN : 1 ≤ ParamsAdopted2.numStepsAdopted2 (m + 1) := by
    have := Submission.L10.three_le_numStepsAdopted2 (n := m + 1) (by omega); omega
  obtain ⟨ω, hω, hlog⟩ := goodPathAt (q := qC α) (W := windowOfR α p m g)
    (A₀ := A0C (m + 1)) (r := 1) hm1 one_pos hc₃0 hc₃η
    (StateSupply.kSet_A0C hraw) (StateSupply.hq_of_raw hraw) (StateSupply.hne_of_raw hraw)
    (StateSupply.symMat_A0C (m + 1)) hε hbdabs hS hcnt hLb hbudget
  exact ⟨1, 6 * 1 * 1 * Real.sqrt ((m + 1 : ℕ) : ℝ), ChainSetup.coord 0,
    ParamsAdopted2.numStepsAdopted2 (m + 1) - 1, ω, by omega, hω, hlog⟩

end GoodPathFree

/-! ## 12. `hS` — the free-dimension total, from the light contact -/

section FreeTotal

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι] {Ω : Type*} [MeasurableSpace Ω]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

/-- `dim − |C_k| ≤ stoppedFreeDim k` **on `{k < τ}`** — `sum_free_ge_cut`'s `hfree`, and false
after the stopping time (report 82b §2, which is why `ContactIntegrated.sum_free_ge` does not
apply). -/
theorem free_ge_of_lt_tau {η r₀ c₃ : ℝ} {N k : ℕ} (ω : Ω)
    (hω : k < tau q W A₀ ξ η r₀ c₃ N ω) :
    (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) - ((Chain.chain q W A₀ ξ k ω).2.card : ℝ)
      ≤ DriftStopped6.stoppedFreeDim q W A₀ ξ η r₀ c₃ N k ω := by
  have hrep : DriftStopped6.stoppedFreeDim q W A₀ ξ η r₀ c₃ N k ω
      = ((Chain.freeDim q W A₀ ξ k ω : ℕ) : ℝ) := by
    rw [DriftStopped6.stoppedFreeDim_eq, ite_eq_left hω]
  rw [hrep, Chain.freeDim]
  have h := Chain.finrank_freeSub_ge_card q (Chain.chain q W A₀ ξ k ω).2
  have hcast : ((finrank ℝ (EuclideanSpace ℝ (UT n))
      - (Chain.chain q W A₀ ξ k ω).2.card : ℕ) : ℝ)
      ≤ ((finrank ℝ (Chain.freeSub q (Chain.chain q W A₀ ξ k ω).2) : ℕ) : ℝ) := by
    exact_mod_cast h
  have hsub : (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ)
      - ((Chain.chain q W A₀ ξ k ω).2.card : ℝ)
      ≤ ((finrank ℝ (EuclideanSpace ℝ (UT n))
          - (Chain.chain q W A₀ ξ k ω).2.card : ℕ) : ℝ) := by
    by_cases hle : finrank ℝ (EuclideanSpace ℝ (UT n)) ≤ (Chain.chain q W A₀ ξ k ω).2.card
    · rw [Nat.sub_eq_zero_of_le hle]
      have : (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ)
          ≤ ((Chain.chain q W A₀ ξ k ω).2.card : ℝ) := by exact_mod_cast hle
      push_cast
      linarith
    · rw [Nat.cast_sub (by omega : (Chain.chain q W A₀ ξ k ω).2.card
        ≤ finrank ℝ (EuclideanSpace ℝ (UT n)))]
  linarith

variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- **`hS`, derived.**  `GoodPathLight.sum_free_ge_cut` at `Nfun := stoppedFreeDim`,
`Cset := C_k`, `Good k := {k < τ}`, `dd := dim E`, with the contact total rewritten by
`ContactIntegrated.integrated_count_eq` into `(1/h)·∑_{W} intWeight` and bounded by the light
contact. -/
theorem hS_of_intWeight {η r₀ c₃ hstep Θ : ℝ} {N m : ℕ} (hstep0 : 0 < hstep)
    (hξ : ∀ j, Measurable (ξ j)) (hτ : Measurable (tau q W A₀ ξ η r₀ c₃ N))
    (hlight : ∑ x ∈ W, ContactIntegrated.intWeight P
        (fun k ω => (Chain.chain q W A₀ ξ k ω).2) hstep m x ≤ Θ) :
    (m : ℝ) * (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) - Θ / hstep
        - (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ)
          * ∑ k ∈ Finset.range m, P.real {ω | k < tau q W A₀ ξ η r₀ c₃ N ω}ᶜ
      ≤ ∑ k ∈ Finset.range m, ∫ ω,
          DriftStopped6.stoppedFreeDim q W A₀ ξ η r₀ c₃ N k ω ∂P := by
  classical
  set dd : ℝ := (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) with hdd
  have hcut := GoodPathLight.sum_free_ge_cut (μ := P)
    (Cset := fun k ω => (Chain.chain q W A₀ ξ k ω).2)
    (Nfun := fun k => DriftStopped6.stoppedFreeDim q W A₀ ξ η r₀ c₃ N k)
    (Good := fun k => {ω | k < tau q W A₀ ξ η r₀ c₃ N ω}) dd m
    (fun k _ ω hω => free_ge_of_lt_tau ω hω)
    (fun k _ ω => by rw [DriftStopped6.stoppedFreeDim]; positivity)
    (by rw [hdd]; positivity)
    (fun k => hτ (measurableSet_Ioi (a := k)))
    (fun k _ => DriftStopped6.integrable_stoppedFreeDim hξ hτ k)
    (fun k _ => StateInvariant4.integrable_card_chain hξ k)
  have hsplit : ∑ k ∈ Finset.range m,
        (dd - ∫ ω, ((Chain.chain q W A₀ ξ k ω).2.card : ℝ) ∂P
          - dd * P.real {ω | k < tau q W A₀ ξ η r₀ c₃ N ω}ᶜ)
      = (m : ℝ) * dd - (∑ k ∈ Finset.range m, ∫ ω, ((Chain.chain q W A₀ ξ k ω).2.card : ℝ) ∂P)
        - dd * ∑ k ∈ Finset.range m, P.real {ω | k < tau q W A₀ ξ η r₀ c₃ N ω}ᶜ := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      Finset.mul_sum, nsmul_eq_mul]
  rw [hsplit] at hcut
  have hint : ∑ k ∈ Finset.range m,
      hstep * ∫ ω, ((Chain.chain q W A₀ ξ k ω).2.card : ℝ) ∂P
      = ∑ x ∈ W, ContactIntegrated.intWeight P
          (fun k ω => (Chain.chain q W A₀ ξ k ω).2) hstep m x :=
    ContactIntegrated.integrated_count_eq P W _ hstep m
      (fun k ω => Chain.chain_snd_subset_window k ω)
      (fun k x _ => Chain.measurableSet_mem_active hξ k x)
  have hpull : ∑ k ∈ Finset.range m,
      hstep * ∫ ω, ((Chain.chain q W A₀ ξ k ω).2.card : ℝ) ∂P
      = hstep * ∑ k ∈ Finset.range m, ∫ ω, ((Chain.chain q W A₀ ξ k ω).2.card : ℝ) ∂P := by
    rw [Finset.mul_sum]
  have hle : hstep * ∑ k ∈ Finset.range m,
      ∫ ω, ((Chain.chain q W A₀ ξ k ω).2.card : ℝ) ∂P ≤ Θ := by
    rw [← hpull, hint]; exact hlight
  have hdiv : ∑ k ∈ Finset.range m, ∫ ω, ((Chain.chain q W A₀ ξ k ω).2.card : ℝ) ∂P
      ≤ Θ / hstep := by
    rw [le_div_iff₀ hstep0, mul_comm]; exact hle
  linarith

end FreeTotal



/-! ## 13. The good event with the contact count read at an index `K < N` -/

section Cut

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι] {Ω : Type*} [MeasurableSpace Ω]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

/-- **The good event with the contact count read at an index `K < N`.**  `wiredGood'` reads it at
`N`, and that — not `c₃` — is what makes `c₃ = n²` unreachable (report 82a-hinge). -/
def goodCut (r : ℝ) (Wacc : Ω → EuclideanSpace ℝ (UT n))
    (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (thr : ℝ) (N : ℕ) (η : ℝ)
    (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι) (A₀ : EuclideanSpace ℝ (UT n))
    (r₀ c₃ : ℝ) (K : ℕ) : Set Ω :=
  StepGlue.chainGood r Wacc ξ thr N η ∩ StateInvariant.accGood q W A₀ ξ N r₀
    ∩ StateInvariant4.countGood q W A₀ ξ K c₃

theorem measureReal_compl_goodCut_le {P : Measure Ω} [IsProbabilityMeasure P]
    (r : ℝ) (Wacc : Ω → EuclideanSpace ℝ (UT n)) (thr : ℝ) (N : ℕ) (η r₀ c₃ : ℝ) (K : ℕ) :
    P.real (goodCut r Wacc ξ thr N η q W A₀ r₀ c₃ K)ᶜ
      ≤ P.real (StepGlue.chainGood r Wacc ξ thr N η)ᶜ
        + P.real (StateInvariant.accGood q W A₀ ξ N r₀)ᶜ
        + P.real (StateInvariant4.countGood q W A₀ ξ K c₃)ᶜ := by
  have hset : (goodCut r Wacc ξ thr N η q W A₀ r₀ c₃ K)ᶜ
      = ((StepGlue.chainGood r Wacc ξ thr N η)ᶜ
          ∪ (StateInvariant.accGood q W A₀ ξ N r₀)ᶜ)
        ∪ (StateInvariant4.countGood q W A₀ ξ K c₃)ᶜ := by
    rw [goodCut, Set.compl_inter, Set.compl_inter]
  rw [hset]
  refine le_trans (measureReal_union_le _ _) ?_
  have := measureReal_union_le (μ := P) (StepGlue.chainGood r Wacc ξ thr N η)ᶜ
    (StateInvariant.accGood q W A₀ ξ N r₀)ᶜ
  linarith

theorem measurableSet_goodCut (hξ : ∀ j, Measurable (ξ j))
    {Wacc : Ω → EuclideanSpace ℝ (UT n)} (hW : Measurable Wacc) (r thr : ℝ) (N : ℕ)
    (η r₀ c₃ : ℝ) (K : ℕ) :
    MeasurableSet (goodCut r Wacc ξ thr N η q W A₀ r₀ c₃ K) :=
  ((measurableSet_goodEventUT hW r thr).inter (measurableSet_stepGood hξ N η)).inter
    (measurableSet_accGood hξ N r₀) |>.inter (measurableSet_countGood hξ K c₃)

/-- On `goodCut` the state conditions hold at **every** index up to `K`. -/
theorem stateGood_of_goodCut {r : ℝ} {Wacc : Ω → EuclideanSpace ℝ (UT n)} {thr : ℝ} {N : ℕ}
    {η r₀ c₃ : ℝ} {K : ℕ} {ω : Ω} (hω : ω ∈ goodCut r Wacc ξ thr N η q W A₀ r₀ c₃ K)
    (hKN : K < N) {j : ℕ} (hj : j ≤ K) :
    ω ∈ stateGood q W A₀ ξ η r₀ c₃ j :=
  ⟨fun i hi => hω.1.1.2 i (by omega), hω.1.2 j (by omega),
    StateInvariant4.card_le_of_countGood hω.2 hj⟩

/-- Hence the stopping time has not fired by `K`. -/
theorem lt_tau_of_goodCut {r : ℝ} {Wacc : Ω → EuclideanSpace ℝ (UT n)} {thr : ℝ} {N : ℕ}
    {η r₀ c₃ : ℝ} {K : ℕ} {ω : Ω} (hω : ω ∈ goodCut r Wacc ξ thr N η q W A₀ r₀ c₃ K)
    (hKN : K < N) : K < tau q W A₀ ξ η r₀ c₃ N ω := by
  by_contra hcon
  push Not at hcon
  rcases tauOf_le_iff.1 hcon with ⟨j, hjK, hjN, hmem⟩ | hNK
  · exact hmem (stateGood_of_goodCut hω hKN hjK)
  · omega

/-- **`StateBounds` at index `K` on `goodCut`** — `StateInvariant4.stateBounds_wired'`'s proof with
the count taken at `K` directly instead of transported from `N`. -/
theorem stateBounds_goodCut {r : ℝ} {Wacc : Ω → EuclideanSpace ℝ (UT n)} {thr : ℝ} {N : ℕ}
    {η a₀ r₀ c₃ : ℝ} {K : ℕ} {ω : Ω}
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃) (hlt : r₀ + c₃ * η < a₀)
    (hω : ω ∈ goodCut r Wacc ξ thr N η q W A₀ r₀ c₃ K) (hKN : K < N) :
    Discharge.StateBounds (symMat (Chain.chain q W A₀ ξ K ω).1)
      (a₀ - (r₀ + c₃ * η)) (a₀ + (r₀ + c₃ * η)) := by
  have hstep : ∀ j, j < K → ‖StateInvariant.gaussStep q W A₀ ξ j ω‖ ≤ η := fun j hj =>
    le_trans (Submodule.norm_starProjection_apply_le _ _) (hω.1.1.2 j (by omega))
  have hlift : ‖StateInvariant.liftSum q W A₀ ξ K ω‖ ≤ c₃ * η := by
    refine le_trans (LiftBound.norm_liftSum_le_card hA₀ hq hne hη K ω hstep) ?_
    exact mul_le_mul_of_nonneg_right hω.2 hη
  exact LiftBound.stateBounds_of_chain_count hA₀ hq hne hA₀m hr₀ (by positivity)
    (hω.1.2 K hKN) hlift hlt

theorem stoppedLogDet_eq_of_lt_tau {η r₀ c₃ : ℝ} {N k : ℕ} {ω : Ω}
    (hlt : k < tau q W A₀ ξ η r₀ c₃ N ω) :
    stoppedLogDet q W A₀ ξ η r₀ c₃ N k ω
      = ChainWiring.logDet (Chain.chain q W A₀ ξ k ω).1 := by
  rw [stoppedLogDet, stoppedState, min_eq_left (by omega)]

end Cut

/-! ## Assembly at the cut index -/

section CutAssembly

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}

/-- **The path, with the contact count read at `K < N`.**  Everything is as `goodPathAt` except
that the good event is `goodCut … K` and the drift horizon is `K`; the conversion from the stopped
log-determinant to the chain's own is `stoppedLogDet_eq_of_lt_tau` at `K < τ`, which `goodCut`
supplies without needing `τ = N`. -/
theorem goodPathCut (hn : 2073600 ≤ n) {c₃ ε S b pcnt r : ℝ} {K : ℕ} (hr : 0 < r)
    (hKN : K < ParamsAdopted2.numStepsAdopted2 n)
    (hc₃0 : 0 ≤ c₃) (hc₃η : c₃ * DriftStopped6.etaAdopted n ≤ 1 / 4)
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a0C n • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hε : 0 ≤ ε)
    (hbdabs : ∀ ω, ∀ k, |ChainWiring.chainErr q W A₀
      (ChainSetup.step (Submission.L10.cAdopted n)) k ω| ≤ ε)
    (hS : S ≤ ∑ k ∈ Finset.range K, ∫ ω,
      DriftStopped6.stoppedFreeDim q W A₀ (ChainSetup.step (Submission.L10.cAdopted n))
        (DriftStopped6.etaAdopted n) (DriftStopped6.r0Adopted n) c₃
        (ParamsAdopted2.numStepsAdopted2 n) k ω
      ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))))
    (hcnt : (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))).real
        (StateInvariant4.countGood q W A₀ (ChainSetup.step (Submission.L10.cAdopted n))
          K c₃)ᶜ ≤ pcnt)
    (hLb : logDetLow n c₃ < b)
    (hbudget : (driftRHS n A₀ c₃ ε S - logDetLow n c₃) / (b - logDetLow n c₃)
      + failTotal n pcnt < 1) :
    ∃ ω, ω ∈ goodCut r (ChainSetup.coord 0)
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
    measurable_tau (ChainSetup.filtration (F := EuclideanSpace ℝ (UT n))) hG _
  have hlt := lt_a0C_of_mAt hn hc₃η
  have hinterr := fun k => integrable_stoppedErr (q := q) (W := W) (A₀ := A₀)
    (cq := cqAt n c₃) (ε := ε) hN hA₀ hq hne hA₀m
    (DriftStopped7.etaAdopted_nonneg (n := n)) (DriftStopped7.r0Adopted_nonneg (n := n))
    hc₃0 hlt (cqAt_nonneg hn hc₃η hc₃0) hε hτ hbdabs k
  have hdrift := drift_bound_at (q := q) (W := W) (A₀ := A₀) (m := K)
    hn hc₃0 hc₃η hA₀ hq hne hA₀m hinterr hS hε
    (fun ω k _ => le_trans (le_abs_self _) (hbdabs ω k))
  have hzero : ∫ ω, stoppedLogDet q W A₀ (ChainSetup.step (Submission.L10.cAdopted n))
        (DriftStopped6.etaAdopted n) (DriftStopped6.r0Adopted n) c₃
        (ParamsAdopted2.numStepsAdopted2 n) 0 ω
        ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))
      = ChainWiring.logDet A₀ := by
    simp only [stoppedLogDet_zero]; simp
  rw [hzero] at hdrift
  have hfail : (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))).real
      (goodCut r (ChainSetup.coord 0) (ChainSetup.step (Submission.L10.cAdopted n))
        (6 * r * 1 * Real.sqrt n) (ParamsAdopted2.numStepsAdopted2 n)
        (DriftStopped6.etaAdopted n) q W A₀ (DriftStopped6.r0Adopted n) c₃ K)ᶜ
      ≤ failTotal n pcnt := by
    refine le_trans (measureReal_compl_goodCut_le _ _ _ _ _ _ _ _) ?_
    rw [failTotal]
    have h1 := chainGood_failure (n := n) hn3 hr
    have h2 := accGood_failure (q := q) (W := W) (A₀ := A₀) hn3
    linarith [hcnt]
  obtain ⟨ω, hb, hω⟩ := exists_mem_of_integral_le
    (DriftStopped6.measurable_stoppedLogDet hξm hτ K)
    (DriftStopped6.integrable_stoppedLogDet hN hξm hτ hA₀ hq hne hA₀m
      (DriftStopped7.etaAdopted_nonneg (n := n)) (DriftStopped7.r0Adopted_nonneg (n := n))
      hc₃0 hlt K)
    (L := logDetLow n c₃) (B := driftRHS n A₀ c₃ ε S)
    (fun ω => stoppedLogDet_ge hN hA₀ hq hne hA₀m
      (DriftStopped7.etaAdopted_nonneg (n := n)) (DriftStopped7.r0Adopted_nonneg (n := n))
      hc₃0 hlt K ω)
    hdrift
    (measurableSet_goodCut hξm (ChainSetup.measurable_coord 0) _ _ _ _ _ _ _)
    hfail hLb hbudget
  refine ⟨ω, hω, ?_⟩
  rwa [stoppedLogDet_eq_of_lt_tau (lt_tau_of_goodCut hω hKN)] at hb

/-- **The state triple `DriftStopped8R.StateSupplyAdoptedR` asks for**, produced directly — no
detour through the frozen `StateSupply.GoodPath`, whose `wiredGood'` reads the count at `N`.  At
`c₃ = DriftStopped6.c3Adopted n` the lower bound `mAt n c₃` **is** `DriftStopped6.mAdopted n`. -/
theorem stateTriple_of_cut (hn : 2073600 ≤ n) {c₃ ε S b pcnt r : ℝ} {K : ℕ} (hr : 0 < r)
    (hKN : K < ParamsAdopted2.numStepsAdopted2 n)
    (hc₃0 : 0 ≤ c₃) (hc₃η : c₃ * DriftStopped6.etaAdopted n ≤ 1 / 4)
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a0C n • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hε : 0 ≤ ε)
    (hbdabs : ∀ ω, ∀ k, |ChainWiring.chainErr q W A₀
      (ChainSetup.step (Submission.L10.cAdopted n)) k ω| ≤ ε)
    (hS : S ≤ ∑ k ∈ Finset.range K, ∫ ω,
      DriftStopped6.stoppedFreeDim q W A₀ (ChainSetup.step (Submission.L10.cAdopted n))
        (DriftStopped6.etaAdopted n) (DriftStopped6.r0Adopted n) c₃
        (ParamsAdopted2.numStepsAdopted2 n) k ω
      ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))))
    (hcnt : (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))).real
        (StateInvariant4.countGood q W A₀ (ChainSetup.step (Submission.L10.cAdopted n))
          K c₃)ᶜ ≤ pcnt)
    (hLb : logDetLow n c₃ < b)
    (hbudget : (driftRHS n A₀ c₃ ε S - logDetLow n c₃) / (b - logDetLow n c₃)
      + failTotal n pcnt < 1) :
    ∃ (A : EuclideanSpace ℝ (UT n)) (M : ℝ), A ∈ Chain.kSet q W ∧
      Discharge.StateBounds (symMat A) (mAt n c₃) M ∧ ChainWiring.logDet A ≤ b := by
  obtain ⟨ω, hω, hlog⟩ := goodPathCut hn hr hKN hc₃0 hc₃η hA₀ hq hne hA₀m hε hbdabs hS hcnt
    hLb hbudget
  exact ⟨(Chain.chain q W A₀ (ChainSetup.step (Submission.L10.cAdopted n)) K ω).1,
    MAt n c₃, Chain.chain_fst_mem_kSet hA₀ hq hne K ω,
    stateBounds_goodCut hA₀ hq hne hA₀m (DriftStopped7.etaAdopted_nonneg (n := n))
      (DriftStopped7.r0Adopted_nonneg (n := n)) hc₃0 (lt_a0C_of_mAt hn hc₃η) hω hKN, hlog⟩

end CutAssembly


end Submission.L10.GoodPathBounds

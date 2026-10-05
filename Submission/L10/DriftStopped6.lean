import Submission.L10.DriftStopped5

/-!
# Gate L-10 (`klartag_packing`) — the stopped error integrated, the drift bound, the existence step

Brief 62.  Report 59 §2 left one mechanical identity open and goals (2)–(5) untouched.  The
identity closes in three lines (`integral_affine`); this module then carries the drift side as far
as the tree's own inputs reach.

## What is here

1. **`integral_sum_stoppedErr_le`** — `DriftStopped5.sum_stoppedErr_le` integrated.  Both countings
   survive: `dim E · ε` from the freeze count, `C₁ · 2B` from `MaximalHyp2` read at the single
   random index `τ − 1` (`DriftStopped5.measurable_tau_sub_one`, `StoppedChain.tau_le`,
   `DriftStopped5.IntegrableAtIndex`).
2. **The integrability fields.**  `Discharge.StateBounds` bounds every eigenvalue into `[m, M]`
   (`le_eigenvalues_of_lower`, `GoodEvent.abs_eigenvalues_le_opNorm`), hence
   `m^n ≤ det ≤ M^n` (`det_bounds_of_stateBounds`); with `StoppedChain.stateBounds_stopped` holding
   *everywhere* that makes `stoppedLogDet` bounded, and `ChainWiring.integrable_logDet_of_bounds`
   finishes.  `stoppedFreeDim` is bounded by `dim E`.  Measurability is a finite partition on
   `min k (τ − 1)`, which ranges over `{0, …, k}`.
3. **`drift_bound_stopped`** — `ChainDrift.drift_bound` with the error total supplied as a sum of
   integrals rather than re-derived per step, which is what keeps the freeze counting
   (`logdet_bound_sum'`; report 57 §1 explains why a single pointwise bound would cost `N·ε`).
   `DriftStopped.integral_errCond` moves the bound from `errCond` to `stoppedErr`.
4. **The expectation-to-existence step**, as far as this lane reaches:
   `exists_le_of_integral_le`, the two-event pigeonhole `exists_mem_inter_of_one_lt`, and
   `exists_logDet_le_on_wiredGood'`, which converts a stopped log-determinant bound on a path of
   `StateInvariant4.wiredGood'` into one for the **real** chain
   (`StoppedChain.stoppedState_eq_of_wiredGood'`, horizon `N − 1`).
5. **The adopted constants**, which report 56 item 4 records as free everywhere in
   `DriftStopped4.Brief54Obligation`: `mAdopted`, `cAdopted`, `slackAdopted`, `BAdopted`.

## What is *not* here, and its exact signature

`driftSide'_of_obligation` does not close, and the missing step is **not** probabilistic.  Between
`exists_logDet_le_on_wiredGood'` and `Assembly.ChainOutput Q.alpha g c₀` sits Lemma 5.2's lattice
half — the ellipsoid `A`, the congruence `SᵀAS = 1`, and the avoidance of `α • latR p (m+1) g` —
of which the tree proves only the eq. (68) arithmetic (`Assembly.sqrt_det_le`,
`Assembly.volume_ge_of_logDet_le`).  The report states the missing theorem.

`DriftStopped5.DriftSide'` and `DriftStopped5.chainDelivers_of_sides'` are already the skeleton's
verbatim definitions (`workspace/DischargeSkeleton.lean:66-79`), so they are imported, not re-cut.
-/


namespace Submission.L10.DriftStopped6

open MeasureTheory Matrix Finset Module Submission.L10 Submission.L10.Increments
open Submission.L10.StoppedChain Submission.L10.DriftStopped Submission.L10.DriftStopped4
open Submission.L10.DriftStopped5
open scoped RealInnerProductSpace

/-! ## 1. `StateBounds` bounds the determinant -/

section Det

variable {n : ℕ}

/-- **Every eigenvalue is at least the quadratic form's lower bound.**  The companion of
`GoodEvent.abs_eigenvalues_le_opNorm`, which the tree has and which supplies the upper bound; this
direction is stated nowhere. -/
theorem le_eigenvalues_of_lower {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) {m : ℝ}
    (hlb : ∀ x : EuclideanSpace ℝ (Fin n),
      m * ‖x‖ ^ 2 ≤ ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) A x⟫) (i : Fin n) :
    m ≤ hA.eigenvalues i := by
  set T := Matrix.toEuclideanCLM (𝕜 := ℝ) A with hT
  set v : EuclideanSpace ℝ (Fin n) := hA.eigenvectorBasis i with hv
  have hv1 : ‖v‖ = 1 := hA.eigenvectorBasis.norm_eq_one i
  have hTv : T v = hA.eigenvalues i • v := by
    apply WithLp.ofLp_injective 2
    rw [hT, Matrix.ofLp_toEuclideanCLM]
    simpa using hA.mulVec_eigenvectorBasis i
  have h := hlb v
  rw [hTv, real_inner_smul_right, real_inner_self_eq_norm_sq, hv1] at h
  simpa using h

/-- **`StateBounds` is a two-sided determinant bound.**  `m ≤ λᵢ ≤ M` for every eigenvalue, so
`mⁿ ≤ det A ≤ Mⁿ`.  This is what makes `log det` of the stopped state a bounded function. -/
theorem det_bounds_of_stateBounds {A : Matrix (Fin n) (Fin n) ℝ} {m M : ℝ}
    (hSB : Discharge.StateBounds A m M) : m ^ n ≤ A.det ∧ A.det ≤ M ^ n := by
  have hH : A.IsHermitian := hSB.posDef.isHermitian
  have hlow : ∀ i, m ≤ hH.eigenvalues i := le_eigenvalues_of_lower hH hSB.lower
  have hup : ∀ i, hH.eigenvalues i ≤ M := by
    intro i
    have h1 := GoodEvent.abs_eigenvalues_le_opNorm hH i
    have h2 := hSB.upper
    have h3 := le_abs_self (hH.eigenvalues i)
    linarith
  have hdet : A.det = ∏ i, hH.eigenvalues i := by simpa using hH.det_eq_prod_eigenvalues
  have hm0 : (0 : ℝ) ≤ m := hSB.mpos.le
  constructor
  · have h : ∏ _i : Fin n, m ≤ ∏ i, hH.eigenvalues i :=
      Finset.prod_le_prod₀ (fun i _ => hm0) (fun i _ => hlow i)
    simpa [hdet] using h
  · have h : ∏ i, hH.eigenvalues i ≤ ∏ _i : Fin n, M :=
      Finset.prod_le_prod₀ (fun i _ => le_trans hm0 (hlow i)) (fun i _ => hup i)
    simpa [hdet] using h

/-- `symMat` is linear in the Frobenius coordinates and `det` is a polynomial, so the composite is
continuous — the route to measurability of `logDet`. -/
theorem continuous_symMat_det :
    Continuous fun x : EuclideanSpace ℝ (UT n) => (symMat x).det := by
  refine Continuous.matrix_det (continuous_matrix fun i j => ?_)
  simp only [symMat_apply]
  exact continuous_const.mul (PiLp.continuous_apply 2 (fun _ : UT n => ℝ) (up i j))

end Det

/-! ## 2. The integrability fields -/

section Fields

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι] {Ω : Type*} [m0 : MeasurableSpace Ω]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

theorem measurable_logDet_chain (hξ : ∀ j, Measurable (ξ j)) (j : ℕ) :
    Measurable fun ω => ChainWiring.logDet (Chain.chain q W A₀ ξ j ω).1 := by
  have h1 : Measurable fun ω => (symMat (Chain.chain q W A₀ ξ j ω).1).det :=
    (continuous_symMat_det (n := n)).measurable.comp (Chain.measurable_chain_fst hξ j)
  exact Real.measurable_log.comp h1

/-- **`stoppedLogDet` is measurable.**  `min k (τ − 1)` takes values in `{0, …, k}`, so the stopped
state is a finite sum of indicators of the fibres of a measurable `ℕ`-valued map. -/
theorem measurable_stoppedLogDet (hξ : ∀ j, Measurable (ξ j)) {η r₀ c₃ : ℝ} {N : ℕ}
    (hτ : Measurable (tau q W A₀ ξ η r₀ c₃ N)) (k : ℕ) :
    Measurable (stoppedLogDet q W A₀ ξ η r₀ c₃ N k) := by
  classical
  have hmin : Measurable fun ω => min k (tau q W A₀ ξ η r₀ c₃ N ω - 1) :=
    measurable_const.min (hτ.sub_const 1)
  have hrep : stoppedLogDet q W A₀ ξ η r₀ c₃ N k
      = fun ω => ∑ j ∈ Finset.range (k + 1),
          if min k (tau q W A₀ ξ η r₀ c₃ N ω - 1) = j
            then ChainWiring.logDet (Chain.chain q W A₀ ξ j ω).1 else 0 := by
    funext ω
    rw [Finset.sum_ite_eq (Finset.range (k + 1)) (min k (tau q W A₀ ξ η r₀ c₃ N ω - 1))
      (fun j => ChainWiring.logDet (Chain.chain q W A₀ ξ j ω).1),
      ite_eq_left (Finset.mem_range.2 (by omega))]
    rfl
  rw [hrep]
  refine Finset.measurable_sum _ fun j _ => ?_
  exact Measurable.ite (hmin (measurableSet_singleton j)) (measurable_logDet_chain hξ j)
    measurable_const

/-- **`intD`, the drift's first integrability field.**  `stateBounds_stopped` holds for every `k`
and every `ω`, so the stopped log-determinant is bounded between `n·log m` and `n·log M`. -/
theorem integrable_stoppedLogDet {P : Measure Ω} [IsFiniteMeasure P]
    {η a₀ r₀ c₃ : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hξ : ∀ j, Measurable (ξ j)) (hτ : Measurable (tau q W A₀ ξ η r₀ c₃ N))
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃) (hlt : r₀ + c₃ * η < a₀) (k : ℕ) :
    Integrable (stoppedLogDet q W A₀ ξ η r₀ c₃ N k) P := by
  have hmpos : (0 : ℝ) < a₀ - (r₀ + c₃ * η) := by linarith
  refine ChainWiring.integrable_logDet_of_bounds
    (measurable_stoppedLogDet hξ hτ k).aestronglyMeasurable
    (cL := (a₀ - (r₀ + c₃ * η)) ^ n) (C := (a₀ + (r₀ + c₃ * η)) ^ n) (pow_pos hmpos n)
    (Filter.Eventually.of_forall fun ω => ?_)
  have hSB := stateBounds_stopped (ξ := ξ) (N := N) hN hA₀ hq hne hA₀m hη hr₀ hc₃ hlt k ω
  obtain ⟨h1, h2⟩ := det_bounds_of_stateBounds hSB
  have hpos : 0 < (symMat (stoppedState q W A₀ ξ η r₀ c₃ N k ω)).det := hSB.posDef.det_pos
  have hexp : Real.exp (stoppedLogDet q W A₀ ξ η r₀ c₃ N k ω)
      = (symMat (stoppedState q W A₀ ξ η r₀ c₃ N k ω)).det := by
    rw [stoppedLogDet, ChainWiring.logDet, Real.exp_log hpos]
  rw [hexp]
  exact ⟨h1, h2⟩

/-- **`N_k` for the stopped chain**: the free dimension, cut at `{k < τ}` exactly as `stoppedSub`
is (report 51 §1's second cut). -/
noncomputable def stoppedFreeDim (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι)
    (A₀ : EuclideanSpace ℝ (UT n)) (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (η r₀ c₃ : ℝ)
    (N k : ℕ) (ω : Ω) : ℝ :=
  (finrank ℝ (stoppedSub q W A₀ ξ η r₀ c₃ N k ω) : ℝ)

omit [Countable ι] m0 in
theorem stoppedFreeDim_eq {η r₀ c₃ : ℝ} {N k : ℕ} (ω : Ω) :
    stoppedFreeDim q W A₀ ξ η r₀ c₃ N k ω
      = if k < tau q W A₀ ξ η r₀ c₃ N ω then ((Chain.freeDim q W A₀ ξ k ω : ℕ) : ℝ) else 0 := by
  rw [stoppedFreeDim, stoppedSub]
  by_cases h : k < tau q W A₀ ξ η r₀ c₃ N ω
  · rw [ite_eq_left h, ite_eq_left h, Chain.freeDim]
  · rw [ite_eq_right h, ite_eq_right h]
    simp

theorem measurable_stoppedFreeDim (hξ : ∀ j, Measurable (ξ j)) {η r₀ c₃ : ℝ} {N : ℕ}
    (hτ : Measurable (tau q W A₀ ξ η r₀ c₃ N)) (k : ℕ) :
    Measurable (stoppedFreeDim q W A₀ ξ η r₀ c₃ N k) := by
  have hrep : stoppedFreeDim q W A₀ ξ η r₀ c₃ N k
      = fun ω => if k < tau q W A₀ ξ η r₀ c₃ N ω
          then ((Chain.freeDim q W A₀ ξ k ω : ℕ) : ℝ) else 0 :=
    funext fun ω => stoppedFreeDim_eq ω
  rw [hrep]
  have hset : MeasurableSet {ω | k < tau q W A₀ ξ η r₀ c₃ N ω} := hτ trivial
  exact Measurable.ite hset (ChainWiring.measurable_freeDim hξ k) measurable_const

/-- **`intN`, the drift's second integrability field** — free, as it is for the unstopped chain
(`ChainWiring.integrable_freeDim`): the free dimension never exceeds `dim E`. -/
theorem integrable_stoppedFreeDim {P : Measure Ω} [IsFiniteMeasure P]
    (hξ : ∀ j, Measurable (ξ j)) {η r₀ c₃ : ℝ} {N : ℕ}
    (hτ : Measurable (tau q W A₀ ξ η r₀ c₃ N)) (k : ℕ) :
    Integrable (stoppedFreeDim q W A₀ ξ η r₀ c₃ N k) P := by
  refine ChainWiring.integrable_of_ae_bound
    (measurable_stoppedFreeDim hξ hτ k).aestronglyMeasurable
    (C := (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ)) (Filter.Eventually.of_forall fun ω => ?_)
  rw [stoppedFreeDim, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact_mod_cast Submodule.finrank_le _

end Fields

/-! ## 3. The stopped error, integrated -/

section Integral

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι] {Ω : Type*} [m0 : MeasurableSpace Ω]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The identity report 59 §2 stopped on.**  On a probability measure the integral of a constant
plus a scaled integrable function is that constant plus the scaled integral. -/
theorem integral_affine {C C₁ : ℝ} {g : Ω → ℝ} (hg : Integrable g P) :
    ∫ ω, (C + C₁ * g ω) ∂P = C + C₁ * ∫ ω, g ω ∂P := by
  rw [integral_add (integrable_const _) (hg.const_mul _), integral_const, integral_const_mul]
  simp

/-- **Goal (1): `DriftStopped5.sum_stoppedErr_le`, integrated.**  The freeze counting gives
`dim E · ε`; the middle case is one increment at the random index `τ − 1`, integrable by
`IntegrableAtIndex` and bounded by `MaximalHyp2` through `maximalHyp2_of`. -/
theorem integral_sum_stoppedErr_le (ℱ : Filtration ℕ m0)
    {η a₀ r₀ c₃ c ε B : ℝ} {N m : ℕ}
    (hG : ∀ k, MeasurableSet[ℱ k] (stateGood q W A₀ ξ η r₀ c₃ k))
    (hN : 1 ≤ N) (hc : 0 ≤ c) (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃) (hlt : r₀ + c₃ * η < a₀)
    (hε : 0 ≤ ε) (hbd : ∀ ω : Ω, ∀ k, k < m → ChainWiring.chainErr q W A₀ ξ k ω ≤ ε)
    (hsum : Integrable
      (fun ω => ∑ k ∈ Finset.range m, stoppedErr q W A₀ ξ η r₀ c₃ c N k ω) P)
    (hmax : MaximalHyp2 ξ P N B) (hidx : IntegrableAtIndex P ξ N) :
    ∫ ω, (∑ k ∈ Finset.range m, stoppedErr q W A₀ ξ η r₀ c₃ c N k ω) ∂P
      ≤ (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) * ε
        + C₁ n (a₀ - (r₀ + c₃ * η)) c * (2 * B) := by
  have hmeasf : Measurable (fun ω => tau q W A₀ ξ η r₀ c₃ N ω - 1) :=
    measurable_tau_sub_one ℱ hG N
  have hltN : ∀ ω, tau q W A₀ ξ η r₀ c₃ N ω - 1 < N := by
    intro ω
    have := tau_le (q := q) (W := W) (A₀ := A₀) (ξ := ξ) (η := η) (r₀ := r₀) (c₃ := c₃)
      (N := N) ω
    omega
  obtain ⟨hi1, hi2⟩ := hidx _ hmeasf hltN
  have hm : 0 < a₀ - (r₀ + c₃ * η) := by linarith
  have hC : 0 ≤ C₁ n (a₀ - (r₀ + c₃ * η)) c := C₁_nonneg hc hm
  have hrhsInt : Integrable (fun ω => (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) * ε
      + C₁ n (a₀ - (r₀ + c₃ * η)) c
        * (‖ξ (tau q W A₀ ξ η r₀ c₃ N ω - 1) ω‖
            + ‖ξ (tau q W A₀ ξ η r₀ c₃ N ω - 1) ω‖ ^ 2)) P :=
    (integrable_const _).add ((hi1.add hi2).const_mul _)
  have hmono := integral_mono hsum hrhsInt (fun ω =>
    sum_stoppedErr_le hN hc hA₀ hq hne hA₀m hη hr₀ hc₃ hlt hε (hbd ω))
  have hEq : ∫ ω, ((finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) * ε
        + C₁ n (a₀ - (r₀ + c₃ * η)) c
          * (‖ξ (tau q W A₀ ξ η r₀ c₃ N ω - 1) ω‖
              + ‖ξ (tau q W A₀ ξ η r₀ c₃ N ω - 1) ω‖ ^ 2)) ∂P
      = (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) * ε
        + C₁ n (a₀ - (r₀ + c₃ * η)) c
          * ∫ ω, (‖ξ (tau q W A₀ ξ η r₀ c₃ N ω - 1) ω‖
              + ‖ξ (tau q W A₀ ξ η r₀ c₃ N ω - 1) ω‖ ^ 2) ∂P :=
    integral_affine (hi1.add hi2)
  rw [hEq] at hmono
  have hmaxb := maximalHyp2_of ξ P N hmax hltN hi1 hi2
  nlinarith [hmono, hmaxb, hC]

/-- The same bound on the **sum of the integrals**, which is the shape `ChainDrift.drift_bound`
consumes. -/
theorem sum_integral_stoppedErr_le (ℱ : Filtration ℕ m0)
    {η a₀ r₀ c₃ c ε B : ℝ} {N m : ℕ}
    (hG : ∀ k, MeasurableSet[ℱ k] (stateGood q W A₀ ξ η r₀ c₃ k))
    (hN : 1 ≤ N) (hc : 0 ≤ c) (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃) (hlt : r₀ + c₃ * η < a₀)
    (hε : 0 ≤ ε) (hbd : ∀ ω : Ω, ∀ k, k < m → ChainWiring.chainErr q W A₀ ξ k ω ≤ ε)
    (hint : ∀ k ∈ Finset.range m, Integrable (stoppedErr q W A₀ ξ η r₀ c₃ c N k) P)
    (hmax : MaximalHyp2 ξ P N B) (hidx : IntegrableAtIndex P ξ N) :
    ∑ k ∈ Finset.range m, ∫ ω, stoppedErr q W A₀ ξ η r₀ c₃ c N k ω ∂P
      ≤ (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) * ε
        + C₁ n (a₀ - (r₀ + c₃ * η)) c * (2 * B) := by
  rw [← integral_finsetSum _ hint]
  exact integral_sum_stoppedErr_le ℱ hG hN hc hA₀ hq hne hA₀m hη hr₀ hc₃ hlt hε hbd
    (integrable_finsetSum _ hint) hmax hidx

end Integral

/-! ## 4. The drift bound for the stopped chain -/

section Drift

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι] {Ω : Type*} [m0 : MeasurableSpace Ω]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- **`ContactIntegrated.logdet_bound_sum` with the error total supplied directly.**  That module's
version re-derives the total from a per-step bound and a freeze count; here the total is already a
sum of integrals, which is what `sum_integral_stoppedErr_le` produces and what keeps the middle
case at `O(B)` rather than `O(N·B)` (report 57 §1). -/
theorem logdet_bound_sum' {ℱ : ℕ → MeasurableSpace Ω} {D Nf err : ℕ → Ω → ℝ} {κ : ℝ} {m : ℕ}
    (h : ChainDrift.DriftInputs P ℱ D Nf err κ m) (hκ : 0 ≤ κ) {S E : ℝ}
    (hS : S ≤ ∑ k ∈ Finset.range m, ∫ ω, Nf k ω ∂P)
    (herr : ∑ k ∈ Finset.range m, ∫ ω, err k ω ∂P ≤ E) :
    ∫ ω, D m ω ∂P ≤ ∫ ω, D 0 ω ∂P - κ * S + E := by
  have hmain := ChainDrift.drift_bound h
  have hdrift : κ * S ≤ ∑ k ∈ Finset.range m, κ * ∫ ω, Nf k ω ∂P := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hS hκ
  linarith

omit [Countable ι] in
/-- **Goal (3): the drift bound for the stopped chain.**  `DriftStopped.integral_errCond` is what
lets the conditional representative `errCond` — the one `StepInputs2.driftInputs_step_chain` wants,
because the chain's own error is not `ℱ k`-measurable (report 49 §3) — be replaced by `stoppedErr`
in the error total. -/
theorem drift_bound_stopped {ℱ : Filtration ℕ m0} {η r₀ c₃ c κ : ℝ} {N m : ℕ} {S E : ℝ}
    (hin : ChainDrift.DriftInputs P ⇑ℱ (stoppedLogDet q W A₀ ξ η r₀ c₃ N)
      (stoppedFreeDim q W A₀ ξ η r₀ c₃ N) (errCond P ⇑ℱ q W A₀ ξ η r₀ c₃ c N) κ m)
    (hκ : 0 ≤ κ)
    (hS : S ≤ ∑ k ∈ Finset.range m, ∫ ω, stoppedFreeDim q W A₀ ξ η r₀ c₃ N k ω ∂P)
    (herr : ∑ k ∈ Finset.range m, ∫ ω, stoppedErr q W A₀ ξ η r₀ c₃ c N k ω ∂P ≤ E) :
    ∫ ω, stoppedLogDet q W A₀ ξ η r₀ c₃ N m ω ∂P
      ≤ ∫ ω, stoppedLogDet q W A₀ ξ η r₀ c₃ N 0 ω ∂P - κ * S + E := by
  refine logdet_bound_sum' hin hκ hS ?_
  have hswap : ∀ k ∈ Finset.range m,
      ∫ ω, errCond P (⇑ℱ) q W A₀ ξ η r₀ c₃ c N k ω ∂P
        = ∫ ω, stoppedErr q W A₀ ξ η r₀ c₃ c N k ω ∂P := fun k _ => integral_errCond (hin.le k)
  rw [Finset.sum_congr rfl hswap]
  exact herr

/-- **Goal (3), with the error total already discharged by goal (1).**  The bound the existence
step consumes: `E log det A^τ_m ≤ E log det A₀ − κ·S + dim E·ε + C₁·2B`. -/
theorem drift_bound_stopped_maximal {ℱ : Filtration ℕ m0}
    {η a₀ r₀ c₃ c κ ε B S : ℝ} {N m : ℕ}
    (hin : ChainDrift.DriftInputs P ⇑ℱ (stoppedLogDet q W A₀ ξ η r₀ c₃ N)
      (stoppedFreeDim q W A₀ ξ η r₀ c₃ N) (errCond P ⇑ℱ q W A₀ ξ η r₀ c₃ c N) κ m)
    (hG : ∀ k, MeasurableSet[ℱ k] (stateGood q W A₀ ξ η r₀ c₃ k))
    (hκ : 0 ≤ κ)
    (hS : S ≤ ∑ k ∈ Finset.range m, ∫ ω, stoppedFreeDim q W A₀ ξ η r₀ c₃ N k ω ∂P)
    (hN : 1 ≤ N) (hc : 0 ≤ c) (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃) (hlt : r₀ + c₃ * η < a₀)
    (hε : 0 ≤ ε) (hbd : ∀ ω : Ω, ∀ k, k < m → ChainWiring.chainErr q W A₀ ξ k ω ≤ ε)
    (hint : ∀ k ∈ Finset.range m, Integrable (stoppedErr q W A₀ ξ η r₀ c₃ c N k) P)
    (hmax : MaximalHyp2 ξ P N B) (hidx : IntegrableAtIndex P ξ N) :
    ∫ ω, stoppedLogDet q W A₀ ξ η r₀ c₃ N m ω ∂P
      ≤ ∫ ω, stoppedLogDet q W A₀ ξ η r₀ c₃ N 0 ω ∂P - κ * S
        + ((finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) * ε
            + C₁ n (a₀ - (r₀ + c₃ * η)) c * (2 * B)) :=
  drift_bound_stopped hin hκ hS
    (sum_integral_stoppedErr_le ℱ hG hN hc hA₀ hq hne hA₀m hη hr₀ hc₃ hlt hε hbd hint hmax hidx)

end Drift

/-! ## 5. The existence step -/

section Existence

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι] {Ω : Type*} [m0 : MeasurableSpace Ω]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Expectation to existence.**  On a probability measure an integral bound is attained: if the
function were everywhere above `b`, the integral of the positive difference would be positive. -/
theorem exists_le_of_integral_le {f : Ω → ℝ} (hf : Integrable f P) {b : ℝ}
    (h : ∫ ω, f ω ∂P ≤ b) : ∃ ω, f ω ≤ b := by
  by_contra hcon
  have hcon : ∀ ω, b < f ω := fun ω => lt_of_not_ge fun hle => hcon ⟨ω, hle⟩
  have hsup : Function.support (fun ω => f ω - b) = Set.univ := by
    ext ω
    simp only [Function.mem_support, Set.mem_univ, iff_true, ne_eq, sub_eq_zero]
    exact fun heq => absurd heq (ne_of_gt (hcon ω))
  have hint : Integrable (fun ω => f ω - b) P := hf.sub (integrable_const b)
  have hpos : 0 < ∫ ω, (f ω - b) ∂P := by
    rw [integral_pos_iff_support_of_nonneg_ae
      (Filter.Eventually.of_forall fun ω => by
        simp only [Pi.zero_apply]; linarith [hcon ω]) hint, hsup]
    simp
  rw [integral_sub hf (integrable_const b), integral_const] at hpos
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul] at hpos
  linarith

/-- **The two-event pigeonhole.**  This is how the drift bound and the good event meet: the
log-determinant bound holds on an event, `wiredGood'` on another, and the two must intersect once
their measures sum to more than one (`StateInvariant4.measureReal_compl_wiredGood'_le` is the
tree's bound on the second). -/
theorem exists_mem_inter_of_one_lt {G S : Set Ω} (hS : MeasurableSet S)
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

/-- **Goal (4), as far as this lane reaches.**  On `wiredGood'` the stopped chain *is* the chain
(`StoppedChain.stoppedState_eq_of_wiredGood'`, for every step of the horizon `N − 1`), so a path
that meets both the log-determinant bound and the good event carries that bound for the **real**
chain — which is what Lemma 5.2's lattice half consumes. -/
theorem exists_logDet_le_on_wiredGood' {r : ℝ} {Wacc : Ω → EuclideanSpace ℝ (UT n)} {thr : ℝ}
    {η r₀ c₃ b : ℝ} {N k : ℕ} (hk : k ≤ N - 1)
    (hmeet : ∃ ω, stoppedLogDet q W A₀ ξ η r₀ c₃ N k ω ≤ b
      ∧ ω ∈ StateInvariant4.wiredGood' r Wacc ξ thr N η q W A₀ r₀ c₃) :
    ∃ ω, ω ∈ StateInvariant4.wiredGood' r Wacc ξ thr N η q W A₀ r₀ c₃ ∧
      ChainWiring.logDet (Chain.chain q W A₀ ξ k ω).1 ≤ b := by
  obtain ⟨ω, hb, hg⟩ := hmeet
  refine ⟨ω, hg, ?_⟩
  rwa [stoppedLogDet, stoppedState_eq_of_wiredGood' hg hk] at hb

end Existence

/-! ## 6. The adopted constants

Report 56 item 4: `DriftStopped4.Brief54Obligation` leaves `m`, `c` and `slack` free and nothing in
the tree fixes them, so `SlackHyp`'s `C₁ n m c = c + √n / m` is meaningless until they are.  These
are the values report 57 §2 measures at — `m = 0.9364`, `C₁ = 1538 ≈ 1.07·√n`, `C₁·2B = 3.2·10⁻¹⁸`
at `n = 2 073 600`, against a slack of order `1`. -/

section Adopted

/-- `r₀` at the adopted parameters: the good event's operator-norm threshold `6√(T·n)`, which
`GoodEvent.lean:320` evaluates to `24√(log n / n)`. -/
noncomputable def r0Adopted (n : ℕ) : ℝ := 24 * Real.sqrt (Real.log n / (n : ℝ))

/-- `η` at the adopted parameters: `√(2 h d n)` with `h = ParamsAdopted2.stepSizeAdopted2 n`;
`ParamsAdopted2.eta2_le` bounds it by `√2 · n⁻³`. -/
noncomputable def etaAdopted (n : ℕ) : ℝ :=
  Real.sqrt (2 * ParamsAdopted2.stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ) * (n : ℝ))

/-- `c₃` at the adopted parameters (report 41 §2). -/
noncomputable def c3Adopted (n : ℕ) : ℝ := (n : ℝ) ^ 2

/-- **`m_adopted`**: the state's lower bound `a₀ − (r₀ + c₃η)`, `SlackHyp`'s first free argument.
`a₀ = (1 − 1/n)⁻²` is `Submission.L10.a0C` (`Lemma43Uniform.lean:431`). -/
noncomputable def mAdopted (n : ℕ) : ℝ :=
  a0C n - (r0Adopted n + c3Adopted n * etaAdopted n)

/-- The state's upper bound `M = a₀ + (r₀ + c₃η)`. -/
noncomputable def MAdopted (n : ℕ) : ℝ :=
  a0C n + (r0Adopted n + c3Adopted n * etaAdopted n)

/-- `δ = η / m`, the smallest value `DriftStopped.hpt_stopped`'s `hδ` admits. -/
noncomputable def deltaAdopted (n : ℕ) : ℝ := etaAdopted n / mAdopted n

/-- **`c_adopted`**: the drift's quadratic coefficient `1 / (2 M² (1+δ)²)`, `SlackHyp`'s second
free argument — the `c` at which `DriftStopped.hpt_stopped` is stated. -/
noncomputable def cAdopted (n : ℕ) : ℝ :=
  1 / (2 * MAdopted n ^ 2 * (1 + deltaAdopted n) ^ 2)

/-- **`B_adopted`**: report 57 §2's clean majorant `√h · 5√d · √(log n)` for both moments. -/
noncomputable def BAdopted (n : ℕ) : ℝ :=
  Real.sqrt (ParamsAdopted2.stepSizeAdopted2 n)
    * (5 * Real.sqrt (Fintype.card (UT n) : ℝ) * Real.sqrt (Real.log n))

/-- **`slack_adopted`**: the slack the middle case must fit into, of order `1`. -/
noncomputable def slackAdopted : ℝ := 1

theorem slackHyp_adopted_iff (n : ℕ) {B : ℝ} :
    SlackHyp n (mAdopted n) (cAdopted n) B slackAdopted
      ↔ C₁ n (mAdopted n) (cAdopted n) * (2 * B) ≤ 1 := Iff.rfl

end Adopted

end Submission.L10.DriftStopped6

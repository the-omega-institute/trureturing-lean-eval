import Submission.L10.Chain
import Submission.L10.ChainDrift
import Submission.L10.ChainEllipsoid
import Submission.L10.Increments

/-!
# Gate L-10 (`klartag_packing`) — wiring the chain at `E = ℝ^{n×n}_sym`

Brief 11.  `Chain.lean` and `ChainDrift.lean` (brief 7) are stated for an abstract inner product
space `E` with an abstract family of constraint vectors `q : ι → E`; this module instantiates
them at Klartag's actual data and discharges the hypotheses report 7 §8 listed as **H11, H7, H8,
H6**.

## The model — made once, and *not* a second time

Brief 6 already built `ℝ^{n×n}_sym`: `Submission.L10.Increments` models it as
`EuclideanSpace ℝ (UT n)`, `UT n = {p : Fin n × Fin n // p.1 ≤ p.2}`, with
`symMat : EuclideanSpace ℝ (UT n) → Matrix (Fin n) (Fin n) ℝ` scaling the off-diagonal
coordinates by `1/√2` so that `Increments.sum_symMat_mul_eq_inner` makes the Euclidean inner
product of coordinates *equal* the Frobenius inner product of the matrices.  Nothing is rebuilt
here: every instance `Chain.lean` needs (`NormedAddCommGroup`, `InnerProductSpace ℝ`,
`FiniteDimensional`, `MeasurableSpace`, `BorelSpace`) comes free with `EuclideanSpace`, which is
exactly why that model was the right one.

What is missing and supplied here is the *constraint family* and the dimension:

* `qUT x` — the coordinate vector of `x ⊗ x`, characterised by `symMat (qUT x) i j = x i * x j`;
* `inner_qUT : ⟪qUT x, qUT y⟫ = (x ⬝ᵥ y) ^ 2` — **hinge 1's non-negative correlation**, which is
  what makes the one-sided lift of `Chain.lean` land in `K_L` (report 7 §4.4);
* `inner_qUT_eq_quad : ⟪A, qUT x⟫ = (symMat A *ᵥ x) ⬝ᵥ x` — so `Chain.kSet` really is the set of
  `L`-free matrices and `Chain.freeSub` really is Klartag's `F_A` (eq. 13);
* `finrank_symSpace : finrank ℝ (EuclideanSpace ℝ (UT n)) = n * (n + 1) / 2` — the `d` that
  becomes the `n²` (report 7 §5.3).

## Contents

1. H11 — the constraint family, non-negative correlation, and `finrank`.
2. The adopted parameters `N = 16 n⁵ log n`, `h = n⁻⁷` (report 7 §6.4), as **successors** of
   `ChainDrift.numSteps`/`stepSize`; `ChainDrift.lean` is reported and frozen and is not touched.
3. H7 — `err` defined as the lift's log-det cost, and `hzero` from `Chain.freezes_iff`.
4. H8 — integrability: `intN` outright, `intD`/`interr` from bounds, and the deterministic
   `det A ≥ c_L` half of Klartag eq. (32) with the convexity and symmetry of `E_A` that
   Minkowski's theorem consumes.
5. H6 — the per-freeze cost identity with **no** `‖(A')⁻¹‖_F`, and the numeric `ε` at the
   adopted step size.
6. The instantiated drift bound, with H1-H5, H9, H10 as named hypotheses.
-/

namespace Submission.L10.ChainWiring

open Matrix MeasureTheory Finset Module
open scoped RealInnerProductSpace
open Submission.L10 Submission.L10.Increments

/-! ## 1. H11 — the constraint family `q x = x ⊗ x`, and `dim = n(n+1)/2` -/

variable {n : ℕ}

theorem cc_ne_zero (p : UT n) : cc p ≠ 0 := by
  rw [cc]
  split
  · norm_num
  · positivity

/-- **The constraint vector of a lattice point**: the coordinates of `x ⊗ x` in the model. -/
noncomputable def qUT (x : Fin n → ℝ) : EuclideanSpace ℝ (UT n) :=
  WithLp.toLp 2 fun p => x p.1.1 * x p.1.2 / cc p

@[simp] theorem qUT_apply (x : Fin n → ℝ) (p : UT n) :
    (qUT x) p = x p.1.1 * x p.1.2 / cc p := rfl

/-- `q x` really is `x ⊗ x`. -/
theorem symMat_qUT (x : Fin n → ℝ) (i j : Fin n) : symMat (qUT x) i j = x i * x j := by
  rw [symMat_apply, qUT_apply, mul_comm, div_mul_cancel₀ _ (cc_ne_zero _)]
  rcases le_total i j with h | h
  · rw [up_of_le h]
  · rw [up_comm, up_of_le h]; ring

/-- **`⟪A, q x⟫` is the quadratic form.**  So `Chain.kSet q W` is the set of matrices whose
ellipsoid `E_A = {v | ⟪A v, v⟫ < 1}` (Klartag eq. 9) misses the window, and `Chain.freeSub q C`
is his `F_A` (eq. 13). -/
theorem inner_qUT_eq_quad (A : EuclideanSpace ℝ (UT n)) (x : Fin n → ℝ) :
    ⟪A, qUT x⟫ = (symMat A *ᵥ x) ⬝ᵥ x := by
  rw [← sum_symMat_mul_eq_inner]
  simp only [symMat_qUT]
  rw [dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mulVec, dotProduct, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **Non-negative correlation** — hinge 1's `⟪x ⊗ x, y ⊗ y⟫ = (x ⬝ᵥ y)²`, the hypothesis
`Chain.lift_mem_kSet` runs on. -/
theorem inner_qUT (x y : Fin n → ℝ) : ⟪qUT x, qUT y⟫ = (x ⬝ᵥ y) ^ 2 := by
  rw [← sum_symMat_mul_eq_inner]
  simp only [symMat_qUT]
  rw [sq, dotProduct, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem inner_qUT_nonneg (x y : Fin n → ℝ) : (0 : ℝ) ≤ ⟪qUT x, qUT y⟫ := by
  rw [inner_qUT]; positivity

theorem qUT_ne_zero {x : Fin n → ℝ} (hx : x ≠ 0) : qUT x ≠ 0 := by
  intro h
  have h2 : ⟪qUT x, qUT x⟫ = (0 : ℝ) := by rw [h, inner_zero_left]
  rw [inner_qUT] at h2
  have hd : x ⬝ᵥ x = 0 := by nlinarith [sq_nonneg (x ⬝ᵥ x)]
  refine hx (funext fun i => ?_)
  have hsum : ∑ j, x j * x j = 0 := hd
  have hterm : ∀ j ∈ Finset.univ, (0 : ℝ) ≤ x j * x j := fun j _ => mul_self_nonneg _
  have := (Finset.sum_eq_zero_iff_of_nonneg hterm).1 hsum i (Finset.mem_univ i)
  have : x i = 0 := by nlinarith
  simpa using this

/-! ### The dimension -/

theorem card_UT (n : ℕ) : Fintype.card (UT n) = n * (n + 1) / 2 := by
  classical
  rw [Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype fun a b : Fin n => a ≤ b),
    Fintype.card_sigma]
  have h1 : ∀ i : Fin n, Fintype.card {j : Fin n // i ≤ j} = n - (i : ℕ) := by
    intro i
    rw [Fintype.card_subtype]
    have hset : (Finset.univ.filter fun j : Fin n => i ≤ j) = Finset.Ici i := by
      ext j; simp
    rw [hset, Fin.card_Ici]
  simp_rw [h1]
  rw [Fin.sum_univ_eq_sum_range (fun i => n - i) n]
  have h2 : ∑ i ∈ Finset.range n, (n - i) = ∑ i ∈ Finset.range n, (i + 1) := by
    rw [← Finset.sum_range_reflect (fun i => i + 1) n]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    omega
  rw [h2, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  set S := ∑ i ∈ Finset.range n, i with hS
  have h3 : S * 2 = n * (n - 1) := Finset.sum_range_id_mul_two n
  have h4 : (S + n) * 2 = n * (n + 1) := by
    rcases n with _ | m
    · simp [hS]
    · have : (m + 1) - 1 = m := by omega
      rw [this] at h3
      nlinarith [h3]
  omega

/-- **`dim ℝ^{n×n}_sym = n(n+1)/2`** — the `d` of report 7 §5.3, hence the `n²`. -/
theorem finrank_symSpace (n : ℕ) :
    finrank ℝ (EuclideanSpace ℝ (UT n)) = n * (n + 1) / 2 := by
  rw [finrank_euclideanSpace, card_UT]

/-! ## 2. The adopted parameters — `N = 16 n⁵ log n`, `h = n⁻⁷`

Report 7 §6 showed that hinge 1's `h = n⁻⁵` leaves the freeze corrections at a *constant* fraction
of the scale Corollary 3.2 controls under the strongest overshoot bound anyone has proved, and
divergent under the uniform-over-the-window bound; `h = n⁻⁷` is safe under all three and costs
nothing, because `N` appears in no bound whose size matters.  That choice is recorded here as a
**successor** of `ChainDrift.numSteps`/`stepSize`: `ChainDrift.lean` is reported and frozen
(rule 5) and is not edited. -/

/-- `N = ⌈16 n⁵ log n⌉` — the adopted number of steps. -/
noncomputable def numStepsAdopted (n : ℕ) : ℕ := ChainDrift.numSteps n 5

/-- `h = T / N ≤ n⁻⁷` — the adopted step size. -/
noncomputable def stepSizeAdopted (n : ℕ) : ℝ := ChainDrift.stepSize n 5

/-- The horizon is hit exactly: `N · h = T`. -/
theorem numStepsAdopted_mul_stepSizeAdopted {n : ℕ} (hn : 3 ≤ n) :
    (numStepsAdopted n : ℝ) * stepSizeAdopted n = ChainDrift.horizon n := by
  rw [numStepsAdopted, stepSizeAdopted, ChainDrift.stepSize,
    mul_div_cancel₀ _ (ne_of_gt (ChainDrift.numSteps_pos hn))]

theorem stepSizeAdopted_le {n : ℕ} (hn : 3 ≤ n) : stepSizeAdopted n ≤ 1 / (n : ℝ) ^ 7 := by
  rw [stepSizeAdopted]
  have h : ChainDrift.stepSize n 5 ≤ 1 / (n : ℝ) ^ (5 + 2) := ChainDrift.stepSize_le hn
  norm_num at h ⊢
  exact h

/-- The discretisation-error budget at the adopted step size (report 7 §6.3, model (c)):
`d · overshoot ≤ n² √(n h) ≤ 1/n`, hence `o(1)`. -/
theorem projError_adopted {n : ℕ} (hn : 3 ≤ n) :
    (n : ℝ) ^ 2 * Real.sqrt ((n : ℝ) * stepSizeAdopted n) ≤ 1 / (n : ℝ) :=
  ChainDrift.proj_error_le hn (by norm_num)

/-- The pinned trade-off is untouched by the change of `N`. -/
theorem tradeoff_adopted {n : ℕ} (hn : n ≠ 0) :
    (n : ℝ) ^ 2 * ChainDrift.horizon n / 4 = 4 * Real.log n := ChainDrift.tradeoff hn

/-! ## 3. H7 — `err` is the lift's log-det cost, and it is paid only at freezes -/

section Err

variable {ι : Type*} [DecidableEq ι] {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι}
  {A₀ : EuclideanSpace ℝ (UT n)} {Ω : Type*} {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

/-- `log det` of a point of the model. -/
noncomputable def logDet (A : EuclideanSpace ℝ (UT n)) : ℝ := Real.log (symMat A).det

omit [DecidableEq ι] in
/-- The one-sided lift is the identity when nothing is broken. -/
theorem lift_eq_self_of_violated_empty (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι)
    (A' : EuclideanSpace ℝ (UT n)) (h : Chain.violated q W A' = ∅) :
    Chain.lift q W A' = A' := by
  rw [Chain.lift, h, Finset.sum_empty, add_zero]

/-- **`err`**: the log-det cost of the correction at one step — the entire discretisation error
of the chain. -/
noncomputable def liftCost (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι)
    (A' : EuclideanSpace ℝ (UT n)) : ℝ :=
  logDet (Chain.lift q W A') - logDet A'

omit [DecidableEq ι] in
theorem liftCost_eq_zero_of_violated_empty (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι)
    (A' : EuclideanSpace ℝ (UT n)) (h : Chain.violated q W A' = ∅) : liftCost q W A' = 0 := by
  rw [liftCost, lift_eq_self_of_violated_empty q W A' h, sub_self]

/-- The chain's stepped matrix `A'_{k+1}` before the correction. -/
noncomputable def preState (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι)
    (A₀ : EuclideanSpace ℝ (UT n)) (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (k : ℕ) (ω : Ω) :
    EuclideanSpace ℝ (UT n) :=
  (Chain.chain q W A₀ ξ k ω).1
    + (Chain.freeSub q (Chain.chain q W A₀ ξ k ω).2).starProjection (ξ k ω)

/-- **The chain's `err k`.** -/
noncomputable def chainErr (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι)
    (A₀ : EuclideanSpace ℝ (UT n)) (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (k : ℕ) (ω : Ω) : ℝ :=
  liftCost q W (preState q W A₀ ξ k ω)

/-- The step's log-determinant splits as the Gaussian part plus the error. -/
theorem logDet_chain_succ (k : ℕ) (ω : Ω) :
    logDet (Chain.chain q W A₀ ξ (k + 1) ω).1
      = logDet (preState q W A₀ ξ k ω) + chainErr q W A₀ ξ k ω := by
  simp only [chainErr, liftCost, preState, Chain.chain_succ, Chain.stepTo]
  ring

/-- **H7.**  Off the freeze set the error vanishes — `Chain.freezes_iff` says a freeze is exactly
a non-empty set of newly broken constraints, and the lift is then the identity. -/
theorem chainErr_eq_zero_of_not_freezes (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    {k : ℕ} {ω : Ω} (hfz : ¬ Chain.Freezes q W A₀ ξ k ω) : chainErr q W A₀ ξ k ω = 0 := by
  refine liftCost_eq_zero_of_violated_empty q W _ ?_
  have h := (Chain.freezes_iff hA₀ hq hne k ω).not.1 hfz
  rw [Finset.not_nonempty_iff_eq_empty] at h
  exact h

theorem chainErr_nonpos_of_not_freezes (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    {k : ℕ} {ω : Ω} (hfz : ¬ Chain.Freezes q W A₀ ξ k ω) : chainErr q W A₀ ξ k ω ≤ 0 :=
  le_of_eq (chainErr_eq_zero_of_not_freezes hA₀ hq hne hfz)

end Err

/-! ## 4. H8 — integrability

Three fields of `ChainDrift.DriftInputs`.  `intN` is **free** (`N_k` is a bounded integer);
`intD` and `interr` reduce to a.e. bounds, and the lower bound on `det A_k` is Klartag's eq. (32),
`det A_t ≥ c_L`, which comes from Minkowski's first theorem applied to the `L`-free ellipsoid.
The two hypotheses Minkowski consumes — convexity and central symmetry of `E_A` — are proved
here; the lattice itself is brief 5's. -/

section Integrability

variable {ι : Type*} [DecidableEq ι] [Countable ι] {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι}
  {A₀ : EuclideanSpace ℝ (UT n)} {Ω : Type*} [MeasurableSpace Ω]
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)} {μ : Measure Ω}

/-- The active set is a measurable `Finset`-valued random variable, fibre by fibre. -/
theorem measurableSet_active_eq (hξ : ∀ k, Measurable (ξ k)) (k : ℕ) (c : Finset ι) :
    MeasurableSet {ω | (Chain.chain q W A₀ ξ k ω).2 = c} := by
  by_cases hc : c ⊆ W
  · have hset : {ω | (Chain.chain q W A₀ ξ k ω).2 = c}
        = (⋂ i ∈ (c : Set ι), {ω | i ∈ (Chain.chain q W A₀ ξ k ω).2})
          ∩ ⋂ i ∈ ((W \ c : Finset ι) : Set ι), {ω | i ∈ (Chain.chain q W A₀ ξ k ω).2}ᶜ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Finset.mem_coe,
        Finset.mem_sdiff, Set.mem_compl_iff]
      constructor
      · intro heq
        refine ⟨fun i hi => by rw [heq]; exact hi, fun i hi hmem => ?_⟩
        rw [heq] at hmem
        exact hi.2 hmem
      · rintro ⟨h1, h2⟩
        ext i
        constructor
        · intro hi
          by_contra hic
          exact h2 i ⟨Chain.chain_snd_subset_window k ω hi, hic⟩ hi
        · exact fun hi => h1 i hi
    rw [hset]
    exact MeasurableSet.inter
      (MeasurableSet.biInter (Finset.countable_toSet c)
        fun i _ => Chain.measurableSet_mem_active hξ k i)
      (MeasurableSet.biInter (Finset.countable_toSet (W \ c))
        fun i _ => (Chain.measurableSet_mem_active hξ k i).compl)
  · have hset : {ω | (Chain.chain q W A₀ ξ k ω).2 = c} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro heq
      exact hc (heq ▸ Chain.chain_snd_subset_window k ω)
    rw [hset]
    exact MeasurableSet.empty

/-- **Any real function of the active set is a measurable random variable.**  The active set takes
finitely many values (`Finset.powerset W`), so the composition is a finite sum of indicators. -/
theorem measurable_of_active (hξ : ∀ k, Measurable (ξ k)) (k : ℕ) (f : Finset ι → ℝ) :
    Measurable fun ω => f (Chain.chain q W A₀ ξ k ω).2 := by
  classical
  have hrep : (fun ω => f (Chain.chain q W A₀ ξ k ω).2)
      = fun ω => ∑ c ∈ W.powerset, if (Chain.chain q W A₀ ξ k ω).2 = c then f c else 0 := by
    funext ω
    rw [Finset.sum_ite_eq W.powerset (Chain.chain q W A₀ ξ k ω).2 f,
      ite_eq_left (Finset.mem_powerset.2 (Chain.chain_snd_subset_window k ω))]
  rw [hrep]
  refine Finset.measurable_sum _ fun c _ => ?_
  exact Measurable.ite (measurableSet_active_eq hξ k c) measurable_const measurable_const

/-- `N_k = dim F(C_k)` is measurable. -/
theorem measurable_freeDim (hξ : ∀ k, Measurable (ξ k)) (k : ℕ) :
    Measurable fun ω => ((Chain.freeDim q W A₀ ξ k ω : ℕ) : ℝ) :=
  measurable_of_active hξ k fun c => (finrank ℝ (Chain.freeSub q c) : ℝ)

theorem integrable_of_ae_bound [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ)
    {C : ℝ} (hb : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ C) : Integrable f μ :=
  Integrable.mono' (integrable_const C) hf hb

/-- **`intN` is free.**  `N_k ≤ dim E` pointwise, and a bounded measurable function on a finite
measure is integrable. -/
theorem integrable_freeDim [IsFiniteMeasure μ] (hξ : ∀ k, Measurable (ξ k)) (k : ℕ) :
    Integrable (fun ω => ((Chain.freeDim q W A₀ ξ k ω : ℕ) : ℝ)) μ := by
  refine integrable_of_ae_bound (measurable_freeDim hξ k).aestronglyMeasurable
    (C := (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ)) (.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact_mod_cast Submodule.finrank_le _

/-- **`intD` from a two-sided bound on the determinant.**  The lower bound is Klartag eq. (32),
`det A_t ≥ c_L`, from Minkowski's first theorem (`det_ge_of_volume_le` below); the upper bound is
the good event of Corollary 3.2 (H5). -/
theorem integrable_logDet_of_bounds [IsFiniteMeasure μ] {D : Ω → ℝ}
    (hmeas : AEStronglyMeasurable D μ) {cL C : ℝ} (hcL : 0 < cL)
    (hb : ∀ᵐ ω ∂μ, cL ≤ Real.exp (D ω) ∧ Real.exp (D ω) ≤ C) : Integrable D μ := by
  refine integrable_of_ae_bound hmeas (C := |Real.log cL| + |Real.log C|) ?_
  filter_upwards [hb] with ω hω
  have h1 : Real.log cL ≤ D ω := by
    have := Real.log_le_log hcL hω.1
    rwa [Real.log_exp] at this
  have h2 : D ω ≤ Real.log C := by
    have := Real.log_le_log (lt_of_lt_of_le hcL hω.1) hω.2
    rwa [Real.log_exp] at this
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have := neg_abs_le (Real.log cL); have := abs_nonneg (Real.log C); linarith
  · have := le_abs_self (Real.log C); have := abs_nonneg (Real.log cL); linarith

/-- **`interr` from a bound on the per-step error.** -/
theorem integrable_err_of_bound [IsFiniteMeasure μ] {err : Ω → ℝ}
    (hmeas : AEStronglyMeasurable err μ) {ε : ℝ} (hb : ∀ᵐ ω ∂μ, ‖err ω‖ ≤ ε) :
    Integrable err μ := integrable_of_ae_bound hmeas hb

end Integrability

/-! ### The two hypotheses Minkowski's first theorem consumes, and `det A ≥ c_L`

`Matrix.PosSemidef` at this pin is stated over `n →₀ R` (`LinearAlgebra/Matrix/PosDef.lean:59`),
which is awkward to use here, so — rule 7 — positive semi-definiteness enters as the property
actually needed, `∀ v, 0 ≤ quadForm M v`, and symmetry as `M.IsSymm`.  `Increments.symMat_isSymm`
supplies the latter for every point of the model. -/

section Minkowski

variable {n : ℕ}

/-- The quadratic form of a matrix, `Q_M(v) = ⟪M v, v⟫`. -/
noncomputable def quadForm (M : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) : ℝ := (M *ᵥ v) ⬝ᵥ v

theorem quadForm_eq_inner (A : EuclideanSpace ℝ (UT n)) (x : Fin n → ℝ) :
    ⟪A, qUT x⟫ = quadForm (symMat A) x := inner_qUT_eq_quad A x

theorem bil_symm {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsSymm) (v w : Fin n → ℝ) :
    (M *ᵥ v) ⬝ᵥ w = (M *ᵥ w) ⬝ᵥ v := by
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, hM]

theorem quadForm_add {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsSymm) (a b : ℝ)
    (v w : Fin n → ℝ) :
    quadForm M (a • v + b • w)
      = a ^ 2 * quadForm M v + 2 * (a * b) * ((M *ᵥ v) ⬝ᵥ w) + b ^ 2 * quadForm M w := by
  simp only [quadForm, mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
    dotProduct_smul, smul_eq_mul]
  rw [bil_symm hM w v]
  ring

theorem quadForm_sub {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsSymm) (v w : Fin n → ℝ) :
    quadForm M (v - w) = quadForm M v - 2 * ((M *ᵥ v) ⬝ᵥ w) + quadForm M w := by
  simp only [quadForm, mulVec_sub, sub_dotProduct, dotProduct_sub]
  rw [bil_symm hM w v]
  ring

theorem two_bil_le {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsSymm)
    (hpsd : ∀ v : Fin n → ℝ, 0 ≤ quadForm M v) (v w : Fin n → ℝ) :
    2 * ((M *ᵥ v) ⬝ᵥ w) ≤ quadForm M v + quadForm M w := by
  have h := hpsd (v - w)
  rw [quadForm_sub hM] at h
  linarith

/-- **`E_A` is convex** — one of the two hypotheses of Minkowski's first theorem. -/
theorem convex_ellipsoid {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsSymm)
    (hpsd : ∀ v : Fin n → ℝ, 0 ≤ quadForm M v) :
    Convex ℝ (ChainEllipsoid.ellipsoid M) := by
  intro v hv w hw a b ha hb hab
  have hvq : quadForm M v.ofLp < 1 := hv
  have hwq : quadForm M w.ofLp < 1 := hw
  show quadForm M ((a • v + b • w : EuclideanSpace ℝ (Fin n)).ofLp) < 1
  have hcoe : ((a • v + b • w : EuclideanSpace ℝ (Fin n))).ofLp
      = a • v.ofLp + b • w.ofLp := rfl
  rw [hcoe, quadForm_add hM]
  have hbil := two_bil_le hM hpsd v.ofLp w.ofLp
  have hab0 : 0 ≤ a * b := mul_nonneg ha hb
  have step1 : 2 * (a * b) * ((M *ᵥ v.ofLp) ⬝ᵥ w.ofLp)
      ≤ a * b * (quadForm M v.ofLp + quadForm M w.ofLp) := by nlinarith
  have step2 : a ^ 2 * quadForm M v.ofLp + a * b * (quadForm M v.ofLp + quadForm M w.ofLp)
      + b ^ 2 * quadForm M w.ofLp = a * quadForm M v.ofLp + b * quadForm M w.ofLp := by
    linear_combination (a * quadForm M v.ofLp + b * quadForm M w.ofLp) * hab
  have step3 : a * quadForm M v.ofLp + b * quadForm M w.ofLp < a * 1 + b * 1 := by
    rcases eq_or_lt_of_le ha with ha0 | hapos
    · have hb1 : b = 1 := by linarith
      rw [← ha0, hb1]
      simpa using hwq
    · have h6 : a * quadForm M v.ofLp < a * 1 := mul_lt_mul_of_pos_left hvq hapos
      have h7 : b * quadForm M w.ofLp ≤ b * 1 := mul_le_mul_of_nonneg_left hwq.le hb
      linarith
  have step4 : a * 1 + b * 1 = 1 := by linarith
  linarith

/-- **`E_A` is centrally symmetric** — the other hypothesis. -/
theorem neg_mem_ellipsoid {M : Matrix (Fin n) (Fin n) ℝ} {v : EuclideanSpace ℝ (Fin n)}
    (hv : v ∈ ChainEllipsoid.ellipsoid M) : -v ∈ ChainEllipsoid.ellipsoid M := by
  show quadForm M ((-v : EuclideanSpace ℝ (Fin n)).ofLp) < 1
  have hcoe : ((-v : EuclideanSpace ℝ (Fin n))).ofLp = -v.ofLp := rfl
  rw [quadForm, hcoe, mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]
  exact hv

/-- **Klartag eq. (32), the deterministic half.**  A bound `Vol(E_A) ≤ V` — which Minkowski's
first theorem supplies for an `L`-free ellipsoid, with `V = 2ⁿ · covol(L)` — becomes a *lower*
bound on `det A`, which is what makes `log det A_k` integrable from below. -/
theorem det_ge_of_volume_le {A S : Matrix (Fin n) (Fin n) ℝ} (hApos : 0 < A.det)
    (hS : Sᵀ * A * S = 1) {V : ℝ} (hV : 0 < V)
    (hvol : volume (ChainEllipsoid.ellipsoid A) ≤ ENNReal.ofReal V) :
    ((volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal / V) ^ 2 ≤ A.det := by
  have hball : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have hsqrt : 0 < Real.sqrt A.det := Real.sqrt_pos.2 hApos
  have hvolEq := ChainEllipsoid.volume_ellipsoid hApos hS
  rw [hvolEq, ← ENNReal.ofReal_toReal hball, ← ENNReal.ofReal_mul (by positivity)] at hvol
  set B := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal with hB
  have hB0 : 0 ≤ B := ENNReal.toReal_nonneg
  have hreal : 1 / Real.sqrt A.det * B ≤ V := by
    by_contra hcon
    rw [not_le] at hcon
    exact absurd hvol (not_le.2 ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hV.le).2 hcon))
  have hkey : B / V ≤ Real.sqrt A.det := by
    rw [div_le_iff₀ hV]
    rw [one_div, inv_mul_eq_div, div_le_iff₀ hsqrt] at hreal
    linarith
  have hsq := Real.sq_sqrt hApos.le
  nlinarith [hkey, div_nonneg hB0 hV.le]

end Minkowski

/-! ## 5. H6 — the per-freeze cost, and `ε` at the adopted step size

Report 7 §5 argued that the one-sided lift is used *because* its log-det cost carries no
`‖(A')⁻¹‖_F`.  `inner_lift_sub` is that statement, proved: the cost is a non-negative combination
of the quadratic form at the broken constraints, `∑_i λ_i ⟪B x_i, x_i⟫`, and nothing else. -/

section Overshoot

variable {ι : Type*} [DecidableEq ι] {W : Finset ι} {xs : ι → (Fin n → ℝ)}

omit [DecidableEq ι] in
theorem lift_sub (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι)
    (A' : EuclideanSpace ℝ (UT n)) :
    Chain.lift q W A' - A'
      = ∑ i ∈ Chain.violated q W A', ((1 - ⟪A', q i⟫) / ‖q i‖ ^ 2) • q i := by
  rw [Chain.lift, add_sub_cancel_left]

omit [DecidableEq ι] in
/-- **The correction's cost carries no Frobenius norm.**  With `q i = x_i ⊗ x_i`,
`⟪B, Δ⟫ = ∑_i λ_i · ⟪B x_i, x_i⟫`, so the concavity bound on the log-determinant reads
`∑_i λ_i ⟪(A')⁻¹ x_i, x_i⟫ ≤ λ_min(A')⁻¹ ∑_i λ_i |x_i|²` — one factor of `√n` cheaper than
`‖(A')⁻¹‖_F · ‖Δ‖_F`, which is what the Frobenius projection would force. -/
theorem inner_lift_sub (B A' : EuclideanSpace ℝ (UT n)) :
    ⟪B, Chain.lift (fun i => qUT (xs i)) W A' - A'⟫
      = ∑ i ∈ Chain.violated (fun i => qUT (xs i)) W A',
          ((1 - ⟪A', qUT (xs i)⟫) / ‖qUT (xs i)‖ ^ 2) * quadForm (symMat B) (xs i) := by
  rw [lift_sub, inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_right, quadForm_eq_inner, quadForm_eq_inner]

/-- **Each coefficient is bounded by the step's own increment against that constraint.**  This is
what makes the overshoot `O(√h)` rather than `O(n√h)`: `1 - ⟪A + B, q i⟫ ≤ -⟪B, q i⟫` because
`A` already satisfies the constraint. -/
theorem coeff_le {q : ι → EuclideanSpace ℝ (UT n)} {A B : EuclideanSpace ℝ (UT n)}
    (hA : A ∈ Chain.kSet q W) {i : ι} (hi : i ∈ Chain.violated q W (A + B)) :
    (1 - ⟪A + B, q i⟫) / ‖q i‖ ^ 2 ≤ (-⟪B, q i⟫) / ‖q i‖ ^ 2 := by
  obtain ⟨hiW, _⟩ := Chain.mem_violated.1 hi
  have h1 : (1 : ℝ) ≤ ⟪A, q i⟫ := hA i hiW
  have h2 : ⟪A + B, q i⟫ = ⟪A, q i⟫ + ⟪B, q i⟫ := inner_add_left _ _ _
  refine div_le_div_of_nonneg_right ?_ (sq_nonneg _)
  rw [h2]
  linarith

end Overshoot

/-! ### The numeric budget at the adopted step size -/

/-- The per-freeze overshoot of report 7 §6.3, model (c): the maximum over the `N` steps **and**
the `≤ 2(2ⁿ - 1)` window constraints of a centred Gaussian of variance `≤ h`. -/
noncomputable def logFactor (n : ℕ) : ℝ :=
  Real.log (numStepsAdopted n) + ((n : ℝ) + 1) * Real.log 2

noncomputable def overshootBound (n : ℕ) : ℝ :=
  Real.sqrt (2 * stepSizeAdopted n * logFactor n)

theorem log_numStepsAdopted_le {n : ℕ} (hn : 3 ≤ n) :
    Real.log (numStepsAdopted n) ≤ 6 * (n : ℝ) := by
  have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hlog1 : (1 : ℝ) ≤ Real.log n := ChainDrift.log_pos_of_three hn
  have hlogn : Real.log n ≤ (n : ℝ) - 1 := Real.log_le_sub_one_of_pos hn0
  have hceil : ((numStepsAdopted n : ℕ) : ℝ) ≤ 16 * (n : ℝ) ^ 5 * Real.log n + 1 :=
    le_of_lt (Nat.ceil_lt_add_one (by positivity))
  have hbig : 16 * (n : ℝ) ^ 5 * Real.log n + 1 ≤ 17 * (n : ℝ) ^ 6 := by
    have h1 : (n : ℝ) ^ 5 * Real.log n ≤ (n : ℝ) ^ 6 := by
      have h0 : (n : ℝ) ^ 5 * Real.log n ≤ (n : ℝ) ^ 5 * (n : ℝ) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      calc (n : ℝ) ^ 5 * Real.log n ≤ (n : ℝ) ^ 5 * (n : ℝ) := h0
        _ = (n : ℝ) ^ 6 := by ring
    have h2 : (1 : ℝ) ≤ (n : ℝ) ^ 6 := one_le_pow₀ (by linarith)
    linarith
  have hpos : (0 : ℝ) < ((numStepsAdopted n : ℕ) : ℝ) := ChainDrift.numSteps_pos hn
  have hstep : Real.log (numStepsAdopted n) ≤ Real.log (17 * (n : ℝ) ^ 6) :=
    Real.log_le_log hpos (le_trans hceil hbig)
  have hsplit : Real.log (17 * (n : ℝ) ^ 6) = Real.log 17 + 6 * Real.log n := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast
    ring
  have he3 : (17 : ℝ) ≤ Real.exp 3 := by
    have h1 : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add, ← Real.exp_add]; norm_num
    have h2 := Real.exp_one_gt_d9
    rw [h1]
    nlinarith [Real.exp_pos 1]
  have h17 : Real.log 17 ≤ 3 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    exact he3
  rw [hsplit] at hstep
  linarith

theorem logFactor_le {n : ℕ} (hn : 3 ≤ n) : logFactor n ≤ 7 * (n : ℝ) := by
  have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog2 : Real.log 2 ≤ 0.7 := by
    have := Real.log_two_lt_d9
    linarith
  have h1 := log_numStepsAdopted_le hn
  have h2 : ((n : ℝ) + 1) * Real.log 2 ≤ (n : ℝ) := by
    have hpos : (0 : ℝ) ≤ (n : ℝ) + 1 := by linarith
    nlinarith [Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)]
  rw [logFactor]
  linarith

/-- **The discretisation error is `o(1)` at the adopted step size.**  `d · 2 · ε ≤ 8/n`, against
the budget `4 log n`.  At hinge 1's `h = n⁻⁵` the same quantity is a constant (report 7 §6.3). -/
theorem total_error_adopted {n : ℕ} (hn : 3 ≤ n) :
    ((n : ℝ) * ((n : ℝ) + 1) / 2) * 2 * overshootBound n ≤ 8 / (n : ℝ) := by
  have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hlogn : (0 : ℝ) ≤ Real.log n :=
    le_trans (by norm_num) (ChainDrift.log_pos_of_three hn)
  have hstep0 : 0 ≤ stepSizeAdopted n := by
    rw [stepSizeAdopted, ChainDrift.stepSize, ChainDrift.horizon]
    positivity
  have hsq0 : 0 ≤ Real.sqrt ((n : ℝ) * stepSizeAdopted n) := Real.sqrt_nonneg _
  have hbound : overshootBound n ≤ Real.sqrt (14 * ((n : ℝ) * stepSizeAdopted n)) := by
    rw [overshootBound]
    refine Real.sqrt_le_sqrt ?_
    nlinarith [logFactor_le hn, hstep0]
  have hsplit : Real.sqrt (14 * ((n : ℝ) * stepSizeAdopted n))
      = Real.sqrt 14 * Real.sqrt ((n : ℝ) * stepSizeAdopted n) :=
    Real.sqrt_mul (by norm_num) _
  have hs14 : Real.sqrt 14 ≤ 4 := by
    rw [show (4 : ℝ) = Real.sqrt 16 by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hb2 : overshootBound n ≤ 4 * Real.sqrt ((n : ℝ) * stepSizeAdopted n) := by
    refine le_trans hbound ?_
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right hs14 hsq0
  have hc0 : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) + 1) / 2 * 2 := by positivity
  have hrhs0 : (0 : ℝ) ≤ 4 * Real.sqrt ((n : ℝ) * stepSizeAdopted n) := by positivity
  have hd : (n : ℝ) * ((n : ℝ) + 1) / 2 * 2 ≤ (n : ℝ) ^ 2 * 2 := by nlinarith
  have hproj := projError_adopted hn
  calc ((n : ℝ) * ((n : ℝ) + 1) / 2) * 2 * overshootBound n
      ≤ ((n : ℝ) * ((n : ℝ) + 1) / 2) * 2 * (4 * Real.sqrt ((n : ℝ) * stepSizeAdopted n)) :=
        mul_le_mul_of_nonneg_left hb2 hc0
    _ ≤ (n : ℝ) ^ 2 * 2 * (4 * Real.sqrt ((n : ℝ) * stepSizeAdopted n)) :=
        mul_le_mul_of_nonneg_right hd hrhs0
    _ = 8 * ((n : ℝ) ^ 2 * Real.sqrt ((n : ℝ) * stepSizeAdopted n)) := by ring
    _ ≤ 8 * (1 / (n : ℝ)) := by linarith
    _ = 8 / (n : ℝ) := by ring

/-! ## 6. The instantiated drift bound

One correction to report 7's own `ChainDrift.logdet_bound`, found in the wiring: its freeze
predicate `P : ℕ → Prop` is **ω-independent**, so the theorem is usable pointwise in `ω` but not
directly on the integrated sequence — the freeze set is random, and no ω-independent `P` bounds it.
The fix needs no edit to the frozen module: bound the error sum *pointwise* (where
`Chain.card_freezes_le` applies, for each `ω` separately), then integrate.  That is
`sum_chainErr_le` followed by `integral_sum_chainErr_le` below, and `ChainDrift.drift_bound`
(which does not mention `P`) supplies the rest. -/

section Assembly

variable {ι : Type*} [DecidableEq ι] [Countable ι] {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι}
  {A₀ : EuclideanSpace ℝ (UT n)} {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)} {ℱ : ℕ → MeasurableSpace Ω}

omit [Countable ι] in
/-- **The error sum, pointwise**: at most `dim E` freezes, each costing at most `ε`. -/
theorem sum_chainErr_le (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    {ε : ℝ} (hε : 0 ≤ ε) {m : ℕ} {ω : Ω}
    (hbd : ∀ k, k < m → chainErr q W A₀ ξ k ω ≤ ε) :
    ∑ k ∈ Finset.range m, chainErr q W A₀ ξ k ω
      ≤ (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) * ε := by
  classical
  refine ChainDrift.sum_err_le (P := fun k => Chain.Freezes q W A₀ ξ k ω)
    (fun k _ hnf => chainErr_nonpos_of_not_freezes hA₀ hq hne hnf) hbd hε ?_
  have h := Chain.card_freezes_le (ξ := ξ) hA₀ hq hne m ω
  omega

omit [Countable ι] in
/-- The same bound after integration, for a probability measure. -/
theorem integral_sum_chainErr_le [IsProbabilityMeasure μ] (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    {ε : ℝ} (hε : 0 ≤ ε) {m : ℕ}
    (hint : ∀ k, k < m → Integrable (fun ω => chainErr q W A₀ ξ k ω) μ)
    (hbd : ∀ k, k < m → ∀ᵐ ω ∂μ, chainErr q W A₀ ξ k ω ≤ ε) :
    ∑ k ∈ Finset.range m, ∫ ω, chainErr q W A₀ ξ k ω ∂μ
      ≤ (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) * ε := by
  classical
  have hswap : ∑ k ∈ Finset.range m, ∫ ω, chainErr q W A₀ ξ k ω ∂μ
      = ∫ ω, ∑ k ∈ Finset.range m, chainErr q W A₀ ξ k ω ∂μ :=
    (integral_finsetSum _ fun k hk => hint k (Finset.mem_range.1 hk)).symm
  have hall : ∀ᵐ ω ∂μ, ∀ k ∈ Finset.range m, chainErr q W A₀ ξ k ω ≤ ε := by
    rw [Filter.eventually_all_finset]
    exact fun k hk => hbd k (Finset.mem_range.1 hk)
  have hptwise : ∀ᵐ ω ∂μ, ∑ k ∈ Finset.range m, chainErr q W A₀ ξ k ω
      ≤ (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) * ε := by
    filter_upwards [hall] with ω hω
    exact sum_chainErr_le hA₀ hq hne hε fun k hk => hω k (Finset.mem_range.2 hk)
  rw [hswap]
  calc ∫ ω, ∑ k ∈ Finset.range m, chainErr q W A₀ ξ k ω ∂μ
      ≤ ∫ _ω, (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) * ε ∂μ := by
        refine integral_mono_ae (integrable_finsetSum _ fun k hk =>
          hint k (Finset.mem_range.1 hk)) (integrable_const _) hptwise
    _ = (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) * ε := by
        simp

omit [Countable ι] in
/-- **The chain's drift bound at `E = ℝ^{n×n}_sym`** — Klartag Proposition 3.4, instantiated.

What is still assumed, and by whom (report 7 §8):

* `hin` bundles **H1** (the one-step conditional inequality, briefs 2 × 6, which is where **H2**,
  **H3** and **H5** are consumed) and **H8** (integrability — `intN` is free by
  `integrable_freeDim`, `intD` by `integrable_logDet_of_bounds` with `det_ge_of_volume_le`);
* `hN` is **H9**, the expected accumulated contact count, through
  `Chain.finrank_freeSub_ge`: `b = dim E - E|q(C_m)|`;
* `hbd` is **H6**'s probabilistic half — `ε = overshootBound n` at the adopted step size, from
  report 8's `Padding.max_coord_tail`; `total_error_adopted` prices the conclusion's last term.

**H10** (the lattice transfer) and **H4** (the GOE law) do not appear: they enter downstream, in
`ChainEllipsoid.klartag_of_chain` and in the good event respectively. -/
theorem logdet_bound_chain [IsProbabilityMeasure μ] (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    {κ : ℝ} (hκ : 0 ≤ κ) {m : ℕ}
    (hin : ChainDrift.DriftInputs μ ℱ (fun k ω => logDet (Chain.chain q W A₀ ξ k ω).1)
      (fun k ω => ((Chain.freeDim q W A₀ ξ k ω : ℕ) : ℝ))
      (fun k ω => chainErr q W A₀ ξ k ω) κ m)
    {b ε : ℝ} (hε : 0 ≤ ε)
    (hN : ∀ k, k < m → b ≤ ∫ ω, ((Chain.freeDim q W A₀ ξ k ω : ℕ) : ℝ) ∂μ)
    (hbd : ∀ k, k < m → ∀ᵐ ω ∂μ, chainErr q W A₀ ξ k ω ≤ ε) :
    ∫ ω, logDet (Chain.chain q W A₀ ξ m ω).1 ∂μ
      ≤ logDet A₀ - κ * ((m : ℝ) * b)
        + (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) * ε := by
  have hmain := ChainDrift.drift_bound hin
  have hdrift : κ * ((m : ℝ) * b)
      ≤ ∑ k ∈ Finset.range m, κ * ∫ ω, ((Chain.freeDim q W A₀ ξ k ω : ℕ) : ℝ) ∂μ := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (ChainDrift.sum_ge_of_le hN) hκ
  have herr := integral_sum_chainErr_le (μ := μ) hA₀ hq hne hε
    (fun k hk => hin.interr k hk) hbd
  have hzero : ∫ ω, logDet (Chain.chain q W A₀ ξ 0 ω).1 ∂μ = logDet A₀ := by
    simp [Chain.chain_zero]
  rw [hzero] at hmain
  linarith

end Assembly

end Submission.L10.ChainWiring

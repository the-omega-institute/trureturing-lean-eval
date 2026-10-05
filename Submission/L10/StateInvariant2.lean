import Submission.L10.StateInvariantGlue
import Submission.L10.ParamsAdopted2

/-!
# Gate L-10 (`klartag_packing`), brief 34 — closing the state invariant

Report 29 §6 left four rows.  This module does A, C and the assembly; B (the two half-laws) is §3.

* **A** — `wiredGood := StepGlue.chainGood ∩ StateInvariant.accGood`, the event the invariant
  actually needs, with its failure probability;
* **C** — the per-freeze lift bound `‖liftStep j ω‖ ≤ |V_j| · ‖π_j ξ_j‖`, hence `≤ |V_j| · η` on
  `stepGood`;
* **B** — the two half-laws `map_sum_scaled` consumes, from `Increments.indepFun_frozen_isometry`;
* the assembly `stateInvariant_wired`.

Parameters are `ParamsAdopted2`'s (`h = n⁻⁹`, `N = ⌈16 n⁷ log n⌉`), for the reason report 29 §5
gives: at `h = n⁻⁷` the lift budget `d·η` is `≈ 1/2` and does not fit inside `a₀ − r₀ < 1`.
-/

set_option linter.unusedSectionVars false

namespace Submission.L10.StateInvariant2

open MeasureTheory Matrix Finset Module ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace
open Submission.L10 Submission.L10.Increments Submission.L10.StateInvariant

noncomputable section

/-! ## 1. (A) The wired good event -/

section Wired

variable {n : ℕ} {ι : Type*} [DecidableEq ι] {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

/-- **The event the chain is actually run on**: the accumulated Gaussian bound of report 12, the
per-step bound of report 15, *and* the `N` partial-sum bounds of report 29. -/
def wiredGood (r : ℝ) (Wacc : Ω → EuclideanSpace ℝ (UT n))
    (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (thr : ℝ) (N : ℕ) (η : ℝ)
    (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι) (A₀ : EuclideanSpace ℝ (UT n))
    (r₀ : ℝ) : Set Ω :=
  StepGlue.chainGood r Wacc ξ thr N η ∩ accGood q W A₀ ξ N r₀

theorem wiredGood_subset_chainGood {r : ℝ} {Wacc : Ω → EuclideanSpace ℝ (UT n)} {thr : ℝ}
    {N : ℕ} {η r₀ : ℝ} :
    wiredGood r Wacc ξ thr N η q W A₀ r₀ ⊆ StepGlue.chainGood r Wacc ξ thr N η :=
  Set.inter_subset_left

theorem wiredGood_subset_accGood {r : ℝ} {Wacc : Ω → EuclideanSpace ℝ (UT n)} {thr : ℝ}
    {N : ℕ} {η r₀ : ℝ} :
    wiredGood r Wacc ξ thr N η q W A₀ r₀ ⊆ accGood q W A₀ ξ N r₀ :=
  Set.inter_subset_right

/-- The three failure probabilities add. -/
theorem measureReal_compl_wiredGood_le (r : ℝ) (Wacc : Ω → EuclideanSpace ℝ (UT n)) (thr : ℝ)
    (N : ℕ) (η r₀ : ℝ) :
    P.real (wiredGood r Wacc ξ thr N η q W A₀ r₀)ᶜ
      ≤ P.real (StepGlue.chainGood r Wacc ξ thr N η)ᶜ + P.real (accGood q W A₀ ξ N r₀)ᶜ := by
  have hset : (wiredGood r Wacc ξ thr N η q W A₀ r₀)ᶜ
      = (StepGlue.chainGood r Wacc ξ thr N η)ᶜ ∪ (accGood q W A₀ ξ N r₀)ᶜ := by
    rw [wiredGood, Set.compl_inter]
  rw [hset]
  exact measureReal_union_le _ _

/-- **The union-bound cost at `N = ⌈16 n⁷ log n⌉`** — `Discharge.failure_le`'s successor at the new
`N` (`Discharge.failure_le` is stated for `ChainWiring.numStepsAdopted`, which is frozen). -/
theorem failure_le2 {n : ℕ} (hn : 3 ≤ n) {c : ℝ}
    (hc : c ≤ 4 * Real.exp (-(n : ℝ))
      + ((ParamsAdopted2.numStepsAdopted2 n : ℕ) : ℝ)
        * ((Fintype.card (UT n) : ℝ) * (2 * Real.exp (-(n : ℝ))))) :
    c ≤ (33 * (n : ℝ) ^ 9 * Real.log n + 4) * Real.exp (-(n : ℝ)) := by
  have hexp : (0 : ℝ) < Real.exp (-(n : ℝ)) := Real.exp_pos _
  have hcost := ParamsAdopted2.stepGood_cost2_le hn
  have hrw : ((ParamsAdopted2.numStepsAdopted2 n : ℕ) : ℝ)
        * ((Fintype.card (UT n) : ℝ) * (2 * Real.exp (-(n : ℝ))))
      = (((ParamsAdopted2.numStepsAdopted2 n : ℕ) : ℝ) * ((Fintype.card (UT n) : ℝ) * 2))
        * Real.exp (-(n : ℝ)) := by ring
  rw [hrw] at hc
  nlinarith [hc, hcost, hexp]

end Wired

/-! ## 2. (C) The per-freeze lift bound -/

section Lift

variable {n : ℕ} {ι : Type*} [DecidableEq ι] {Ω : Type*}
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

/-- **The lift at one step is at most the number of newly broken constraints times the step's own
increment.**  The coefficient bound is `ChainWiring.coeff_le` — `1 − ⟪A + B, q i⟫ ≤ −⟪B, q i⟫`
because `A` already satisfies the constraint — and then Cauchy–Schwarz. -/
theorem norm_liftStep_le (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0) (k : ℕ) (ω : Ω) :
    ‖liftStep q W A₀ ξ k ω‖
      ≤ ((Chain.newActive q W A₀ ξ k ω).card : ℝ) * ‖gaussStep q W A₀ ξ k ω‖ := by
  classical
  set A := (Chain.chain q W A₀ ξ k ω).1 with hA
  set B := gaussStep q W A₀ ξ k ω with hB
  have hAk : A ∈ Chain.kSet q W := Chain.chain_fst_mem_kSet hA₀ hq hne k ω
  have hsub : liftStep q W A₀ ξ k ω
      = ∑ i ∈ Chain.violated q W (A + B), ((1 - ⟪A + B, q i⟫) / ‖q i‖ ^ 2) • q i := by
    rw [liftStep]
    exact ChainWiring.lift_sub q W _
  have hterm : ∀ i ∈ Chain.violated q W (A + B),
      ‖((1 - ⟪A + B, q i⟫) / ‖q i‖ ^ 2) • q i‖ ≤ ‖B‖ := by
    intro i hi
    obtain ⟨hiW, hilt⟩ := Chain.mem_violated.1 hi
    have hqne : q i ≠ 0 := hne i hiW
    have hq0 : (0 : ℝ) < ‖q i‖ := norm_pos_iff.2 hqne
    have hlam0 : (0 : ℝ) ≤ (1 - ⟪A + B, q i⟫) / ‖q i‖ ^ 2 := by
      apply div_nonneg (by linarith) (by positivity)
    have hle := ChainWiring.coeff_le hAk hi
    have hcs : |⟪B, q i⟫| ≤ ‖B‖ * ‖q i‖ := abs_real_inner_le_norm _ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hlam0]
    rw [div_mul_eq_mul_div, pow_two]
    rw [div_le_iff₀ (by positivity)]
    have h1 : (1 - ⟪A + B, q i⟫) ≤ -⟪B, q i⟫ := by
      have h2 := (div_le_div_iff_of_pos_right (by positivity : (0:ℝ) < ‖q i‖ ^ 2)).1 hle
      linarith
    nlinarith [hcs, abs_le.1 hcs, hq0, h1]
  calc ‖liftStep q W A₀ ξ k ω‖
      = ‖∑ i ∈ Chain.violated q W (A + B), ((1 - ⟪A + B, q i⟫) / ‖q i‖ ^ 2) • q i‖ := by
        rw [hsub]
    _ ≤ ∑ i ∈ Chain.violated q W (A + B), ‖((1 - ⟪A + B, q i⟫) / ‖q i‖ ^ 2) • q i‖ :=
        norm_sum_le _ _
    _ ≤ ((Chain.violated q W (A + B)).card : ℝ) * ‖B‖ := by
        rw [← nsmul_eq_mul]
        exact Finset.sum_le_card_nsmul _ _ _ hterm
    _ = ((Chain.newActive q W A₀ ξ k ω).card : ℝ) * ‖B‖ := rfl

/-- On the step-good event, the increment is at most `η`, so the lift at one step is at most
`|V_k| · η`. -/
theorem norm_liftStep_le_of_stepGood (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    {N : ℕ} {η : ℝ} {ω : Ω} (hω : ω ∈ StepInputs2.stepGood ξ N η) {k : ℕ} (hk : k < N)
    {cV : ℕ} (hcard : (Chain.newActive q W A₀ ξ k ω).card ≤ cV) (_hη : 0 ≤ η) :
    ‖liftStep q W A₀ ξ k ω‖ ≤ (cV : ℝ) * η := by
  have hstep : ‖gaussStep q W A₀ ξ k ω‖ ≤ η :=
    le_trans (Submodule.norm_starProjection_apply_le _ _) (hω k hk)
  have hcardR : ((Chain.newActive q W A₀ ξ k ω).card : ℝ) ≤ (cV : ℝ) := by exact_mod_cast hcard
  have h0 : (0 : ℝ) ≤ ((Chain.newActive q W A₀ ξ k ω).card : ℝ) := Nat.cast_nonneg _
  calc ‖liftStep q W A₀ ξ k ω‖
      ≤ ((Chain.newActive q W A₀ ξ k ω).card : ℝ) * ‖gaussStep q W A₀ ξ k ω‖ :=
        norm_liftStep_le hA₀ hq hne k ω
    _ ≤ (cV : ℝ) * η := mul_le_mul hcardR hstep (norm_nonneg _) (by positivity)

end Lift

/-! ## 3. (B) The frozen rotation at scale `c`, and the chain as a function of its past

These are the two halves of row B that are proved.  `map_sum_scaled` (report 29) needs, for each of
the two sums `Σ_{j<k} ξ_j` and `Σ_{j<k} R_j ξ_j`, a per-step law and a per-step independence.  The
law and the independence for the *reflected* increment are `map_frozen_isometry_scaled` and
`indepFun_frozen_isometry_scaled` below, whose hypothesis is that the reflection is a measurable
function of the past — which is `measurable_U_uncurry`.  What is **not** here is the last plumbing
step, `IndepFun (past ξ k) (ξ k) P` from `iIndepFun ξ P`; see the report. -/

section Scaled

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- A linear isometry preserves `N(0, c²·Id)`, not just the standard Gaussian. -/
theorem scaled_map_isometry (c : ℝ) (U : E ≃ₗᵢ[ℝ] E) :
    (scaled c E).map U = scaled c E := by
  have hcomm : (U : E → E) ∘ (fun x : E => c • x) = (fun x : E => c • x) ∘ (U : E → E) := by
    funext x; simp [map_smul]
  rw [scaled, Measure.map_map U.continuous.measurable (by fun_prop), hcomm,
    ← Measure.map_map (by fun_prop) U.continuous.measurable, Increments.map_stdGaussian_isometry]

variable {α : Type*} [MeasurableSpace α]

/-- The frozen rotation at the level of joint laws, for `N(0, c²·Id)`. -/
theorem map_prod_isometry_scaled (c : ℝ) (μ : Measure α) [SFinite μ] (U : α → (E ≃ₗᵢ[ℝ] E))
    (hU : Measurable fun p : α × E => U p.1 p.2) :
    (μ.prod (scaled c E)).map (fun p => (p.1, U p.1 p.2)) = μ.prod (scaled c E) := by
  have hmeas : Measurable fun p : α × E => (p.1, U p.1 p.2) := measurable_fst.prodMk hU
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply hmeas hs, Measure.prod_apply (hmeas hs), Measure.prod_apply hs]
  refine lintegral_congr fun a => ?_
  have hpre : (Prod.mk a ⁻¹' ((fun p : α × E => (p.1, U p.1 p.2)) ⁻¹' s))
      = (U a) ⁻¹' (Prod.mk a ⁻¹' s) := rfl
  rw [hpre, ← Measure.map_apply (U a).continuous.measurable (measurable_prodMk_left hs),
    scaled_map_isometry]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem map_prod_eq_of_indepFun_scaled {c : ℝ} {Z : Ω → α} {ξ : Ω → E}
    (hZ : Measurable Z) (hξ : Measurable ξ) (hindep : IndepFun Z ξ P)
    (hlaw : P.map ξ = scaled c E)
    (U : α → (E ≃ₗᵢ[ℝ] E)) (hU : Measurable fun p : α × E => U p.1 p.2) :
    P.map (fun ω => (Z ω, U (Z ω) (ξ ω))) = P.map (fun ω => (Z ω, ξ ω)) := by
  have hpair : P.map (fun ω => (Z ω, ξ ω)) = (P.map Z).prod (scaled c E) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hZ.aemeasurable hξ.aemeasurable).1 hindep, hlaw]
  have hcomp : (fun ω => (Z ω, U (Z ω) (ξ ω)))
      = (fun p : α × E => (p.1, U p.1 p.2)) ∘ (fun ω => (Z ω, ξ ω)) := rfl
  rw [hcomp, ← Measure.map_map (measurable_fst.prodMk hU) (hZ.prodMk hξ), hpair,
    map_prod_isometry_scaled c _ U hU]

/-- **The frozen rotation preserves the law, at scale `c`.** -/
theorem map_frozen_isometry_scaled {c : ℝ} {Z : Ω → α} {ξ : Ω → E}
    (hZ : Measurable Z) (hξ : Measurable ξ) (hindep : IndepFun Z ξ P)
    (hlaw : P.map ξ = scaled c E)
    (U : α → (E ≃ₗᵢ[ℝ] E)) (hU : Measurable fun p : α × E => U p.1 p.2) :
    P.map (fun ω => U (Z ω) (ξ ω)) = scaled c E := by
  have hUZ : Measurable fun ω => U (Z ω) (ξ ω) := hU.comp (hZ.prodMk hξ)
  have h := map_prod_eq_of_indepFun_scaled hZ hξ hindep hlaw U hU
  have e1 : P.map (fun ω => U (Z ω) (ξ ω))
      = (P.map (fun ω => (Z ω, U (Z ω) (ξ ω)))).map Prod.snd := by
    rw [Measure.map_map measurable_snd (hZ.prodMk hUZ)]; rfl
  have e2 : P.map ξ = (P.map (fun ω => (Z ω, ξ ω))).map Prod.snd := by
    rw [Measure.map_map measurable_snd (hZ.prodMk hξ)]; rfl
  rw [e1, h, ← e2, hlaw]

/-- **…and it stays independent of the past, at scale `c`.** -/
theorem indepFun_frozen_isometry_scaled {c : ℝ} {Z : Ω → α} {ξ : Ω → E}
    (hZ : Measurable Z) (hξ : Measurable ξ) (hindep : IndepFun Z ξ P)
    (hlaw : P.map ξ = scaled c E)
    (U : α → (E ≃ₗᵢ[ℝ] E)) (hU : Measurable fun p : α × E => U p.1 p.2) :
    IndepFun Z (fun ω => U (Z ω) (ξ ω)) P := by
  have hUZ : Measurable fun ω => U (Z ω) (ξ ω) := hU.comp (hZ.prodMk hξ)
  rw [indepFun_iff_map_prod_eq_prod_map_map hZ.aemeasurable hUZ.aemeasurable,
    map_prod_eq_of_indepFun_scaled hZ hξ hindep hlaw U hU,
    (indepFun_iff_map_prod_eq_prod_map_map hZ.aemeasurable hξ.aemeasurable).1 hindep, hlaw,
    map_frozen_isometry_scaled hZ hξ hindep hlaw U hU]

end Scaled

section Past

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}

/-- The chain at step `k` reads only `ξ j` for `j < k`. -/
theorem chain_congr {Ω Ω' : Type*} {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}
    {ξ' : ℕ → Ω' → EuclideanSpace ℝ (UT n)} {ω : Ω} {ω' : Ω'} (k : ℕ)
    (h : ∀ j, j < k → ξ j ω = ξ' j ω') :
    Chain.chain q W A₀ ξ k ω = Chain.chain q W A₀ ξ' k ω' := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Chain.chain_succ, Chain.chain_succ,
      ih (fun j hj => h j (lt_trans hj (Nat.lt_succ_self k))), h k (Nat.lt_succ_self k)]

/-- The past of the increments, truncated at `k`. -/
def past {Ω : Type*} (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (k : ℕ) (ω : Ω) :
    ℕ → EuclideanSpace ℝ (UT n) := fun j => if j < k then ξ j ω else 0

/-- The chain read as a function of the past sequence. -/
def chainU (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι) (A₀ : EuclideanSpace ℝ (UT n))
    (k : ℕ) (v : ℕ → EuclideanSpace ℝ (UT n)) : EuclideanSpace ℝ (UT n) × Finset ι :=
  Chain.chain q W A₀ (fun j (u : ℕ → EuclideanSpace ℝ (UT n)) => u j) k v

theorem chain_eq_chainU {Ω : Type*} (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (k : ℕ) (ω : Ω) :
    Chain.chain q W A₀ ξ k ω = chainU q W A₀ k (past ξ k ω) :=
  chain_congr k fun j hj => by simp [past, hj]

/-- The frozen reflection attached to an active set. -/
def reflOf (q : ι → EuclideanSpace ℝ (UT n)) (a : Finset ι) :
    EuclideanSpace ℝ (UT n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (UT n) :=
  Submodule.reflection (Chain.freeSub q a)

/-- **The frozen reflection is jointly measurable in `(past, increment)`.**  Proved by hand over
the countable partition by the active set, so that no σ-algebra on `Finset ι` is ever introduced:
putting `⊤` on `Finset ι` and calling `measurable_from_prod_countable_right` sends the unifier into
a blow-up against `EuclideanSpace`'s `comap` measurable space (see the report). -/
theorem measurable_U_uncurry (k : ℕ) :
    Measurable fun p : (ℕ → EuclideanSpace ℝ (UT n)) × EuclideanSpace ℝ (UT n) =>
      reflOf q (chainU q W A₀ k p.1).2 p.2 := by
  intro s hs
  have hset : (fun p : (ℕ → EuclideanSpace ℝ (UT n)) × EuclideanSpace ℝ (UT n) =>
        reflOf q (chainU q W A₀ k p.1).2 p.2) ⁻¹' s
      = ⋃ a : Finset ι,
          ({v : ℕ → EuclideanSpace ℝ (UT n) | (chainU q W A₀ k v).2 = a}
            ×ˢ ((reflOf q a) ⁻¹' s)) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_prod, Set.mem_ofPred_eq]
    constructor
    · intro h
      exact ⟨(chainU q W A₀ k p.1).2, rfl, h⟩
    · rintro ⟨a, ha, h⟩
      rw [ha]
      exact h
  rw [hset]
  refine MeasurableSet.iUnion fun a => MeasurableSet.prod ?_ ?_
  · exact ChainWiring.measurableSet_active_eq
      (ξ := fun j (u : ℕ → EuclideanSpace ℝ (UT n)) => u j)
      (fun j => measurable_pi_apply j) k a
  · exact (reflOf q a).continuous.measurable hs

end Past

/-! ## 4. The invariant and `hpt` on the wired event -/

section Assembly

variable {n : ℕ} {ι : Type*} [DecidableEq ι] {Ω : Type*} [MeasurableSpace Ω]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

/-- **The state invariant on the wired event**, with the lift bound discharged by (C).  The only
inputs are the chain's own hypotheses, a bound `cV` on the number of constraints broken at one
step, and the numeric condition. -/
theorem stateBounds_wired {r : ℝ} {Wacc : Ω → EuclideanSpace ℝ (UT n)} {thr : ℝ} {N : ℕ}
    {η a₀ r₀ : ℝ} {cV : ℕ}
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀)
    (hcard : ∀ k, k < N → ∀ ω : Ω, (Chain.newActive q W A₀ ξ k ω).card ≤ cV)
    (hlt : r₀ + (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) * ((cV : ℝ) * η) < a₀) :
    ∀ k, k < N → ∀ ω ∈ wiredGood r Wacc ξ thr N η q W A₀ r₀,
      Discharge.StateBounds (symMat (Chain.chain q W A₀ ξ k ω).1)
        (a₀ - (r₀ + (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) * ((cV : ℝ) * η)))
        (a₀ + (r₀ + (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) * ((cV : ℝ) * η))) := by
  intro k hk ω hω
  refine StateInvariantGlue.stateBounds_of_chain hA₀ hq hne hA₀m
    (by positivity) hr₀ (hω.2 k hk) (fun j hj => ?_) hlt
  exact norm_liftStep_le_of_stepGood hA₀ hq hne hω.1.2 (lt_trans hj hk)
    (hcard j (lt_trans hj hk) ω) hη

/-- **`hpt` on the wired event** — the last hypothesis of `StepInputs2.driftInputs_step_chain`,
with the state invariant discharged.  This is the hand-off. -/
theorem hpt_wired {r : ℝ} {Wacc : Ω → EuclideanSpace ℝ (UT n)} {thr : ℝ} {N : ℕ}
    {η a₀ r₀ δ : ℝ} {cV : ℕ}
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀)
    (hcard : ∀ k, k < N → ∀ ω : Ω, (Chain.newActive q W A₀ ξ k ω).card ≤ cV)
    (hlt : r₀ + (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) * ((cV : ℝ) * η) < a₀)
    (hδ : η / (a₀ - (r₀ + (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) * ((cV : ℝ) * η))) ≤ δ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    ∀ k, k < N → ∀ ω ∈ wiredGood r Wacc ξ thr N η q W A₀ r₀,
      ChainWiring.logDet (Chain.chain q W A₀ ξ (k + 1) ω).1
        ≤ ChainWiring.logDet (Chain.chain q W A₀ ξ k ω).1
          + ⟪(Chain.freeSub q (Chain.chain q W A₀ ξ k ω).2).starProjection
              (Discharge.matToUT (symMat (Chain.chain q W A₀ ξ k ω).1)⁻¹), ξ k ω⟫
          - (1 / (2 * (a₀ + (r₀ + (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ)
                * ((cV : ℝ) * η))) ^ 2 * (1 + δ) ^ 2))
            * ‖(Chain.freeSub q (Chain.chain q W A₀ ξ k ω).2).starProjection (ξ k ω)‖ ^ 2
          + ChainWiring.chainErr q W A₀ ξ k ω := by
  intro k hk ω hω
  exact Discharge.hpt_step
    (stateBounds_wired hA₀ hq hne hA₀m hη hr₀ hcard hlt k hk ω hω)
    (StepInputs2.opNorm_step_le_of_stepGood hω.1.2 hk _) hδ hδ0 hδ1

/-- **`DischargeGlue.StateInvariant` itself**, for a successor whose `chainGood` parameters already
force the accumulated bound.  When the successor's event is `wiredGood`, `hsub` is
`Set.inter_subset_right` and the two statements coincide. -/
theorem stateInvariant_wired {r : ℝ} {Wacc : Ω → EuclideanSpace ℝ (UT n)} {thr : ℝ} {N : ℕ}
    {η a₀ r₀ : ℝ} {cV : ℕ}
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀)
    (hsub : StepGlue.chainGood r Wacc ξ thr N η ⊆ accGood q W A₀ ξ N r₀)
    (hcard : ∀ k, k < N → ∀ ω : Ω, (Chain.newActive q W A₀ ξ k ω).card ≤ cV)
    (hlt : r₀ + (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) * ((cV : ℝ) * η) < a₀) :
    DischargeGlue.StateInvariant q W A₀ ξ r Wacc thr N η
      (a₀ - (r₀ + (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) * ((cV : ℝ) * η)))
      (a₀ + (r₀ + (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) * ((cV : ℝ) * η))) := by
  refine StateInvariantGlue.stateInvariant_of_accGood hA₀ hq hne hA₀m (by positivity) hr₀ hsub
    (fun k hk ω hω j hj => ?_) hlt
  exact norm_liftStep_le_of_stepGood hA₀ hq hne hω.2 (lt_trans hj hk)
    (hcard j (lt_trans hj hk) ω) hη

end Assembly

end

end Submission.L10.StateInvariant2

import Submission.L10.StateInvariant3

/-!
# Gate L-10 (`klartag_packing`), brief 38 — the lift bound without `cV`

Brief 36 §3 reported `cV` — a per-step bound on the number of constraints broken at one freeze —
as not dischargeable, and brief 38 offered three routes.  Routes L and C are refuted (report 38
§1).  This module takes a fourth: **the `newActive` sets are pairwise disjoint and their union is
the active set**, so the *accumulated* lift is bounded by the *accumulated contact count* times the
per-step increment — no per-step count, and no factor `dim ℝ^{n×n}_sym`:

`‖Σ_{j<k} Δ_j‖ ≤ Σ_{j<k} |V_j| · η = |C_k| · η`.

`|C_k|` is the quantity Klartag already controls (report 7 §8's H9, `E|q(C_m)| = O(1)`), so it is
an input the tree carries anyway rather than a new modelling constant.
-/


namespace Submission.L10.LiftBound

open MeasureTheory Matrix Finset Module ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace
open Submission.L10 Submission.L10.Increments Submission.L10.StateInvariant
open Submission.L10.StateInvariant2

noncomputable section

variable {n : ℕ} {ι : Type*} [DecidableEq ι] {Ω : Type*}
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

/-- **The freezes partition the active set.**  A step never breaks an already-active constraint
(`Chain.newActive_disjoint`), so the counts add. -/
theorem sum_card_newActive (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0) (k : ℕ) (ω : Ω) :
    ∑ j ∈ Finset.range k, (Chain.newActive q W A₀ ξ j ω).card
      = (Chain.chain q W A₀ ξ k ω).2.card := by
  classical
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, Chain.chain_snd_succ_eq,
      Finset.card_union_of_disjoint (Chain.newActive_disjoint hA₀ hq hne k ω).symm]

/-- **The accumulated lift, with no per-step count and no `dim`.** -/
theorem norm_liftSum_le_card (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    {η : ℝ} (_hη0 : 0 ≤ η) (k : ℕ) (ω : Ω)
    (hstep : ∀ j, j < k → ‖gaussStep q W A₀ ξ j ω‖ ≤ η) :
    ‖liftSum q W A₀ ξ k ω‖ ≤ ((Chain.chain q W A₀ ξ k ω).2.card : ℝ) * η := by
  classical
  have hterm : ∀ j ∈ Finset.range k,
      ‖liftStep q W A₀ ξ j ω‖ ≤ ((Chain.newActive q W A₀ ξ j ω).card : ℝ) * η := by
    intro j hj
    refine le_trans (norm_liftStep_le hA₀ hq hne j ω) ?_
    exact mul_le_mul_of_nonneg_left (hstep j (Finset.mem_range.1 hj)) (Nat.cast_nonneg _)
  calc ‖liftSum q W A₀ ξ k ω‖
      ≤ ∑ j ∈ Finset.range k, ‖liftStep q W A₀ ξ j ω‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range k, ((Chain.newActive q W A₀ ξ j ω).card : ℝ) * η :=
        Finset.sum_le_sum hterm
    _ = (∑ j ∈ Finset.range k, ((Chain.newActive q W A₀ ξ j ω).card : ℝ)) * η := by
        rw [Finset.sum_mul]
    _ = ((Chain.chain q W A₀ ξ k ω).2.card : ℝ) * η := by
        rw [← Nat.cast_sum, sum_card_newActive hA₀ hq hne k ω]

/-! ## The state invariant with the lift bound of this module -/

section Wired

variable [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- The per-path core with the **accumulated** lift bound (`StateInvariantGlue.stateBounds_of_chain`
takes the per-step one and pays a factor `dim`). -/
theorem stateBounds_of_chain_count {a₀ r₀ L : ℝ} {k : ℕ} {ω : Ω}
    (_hA₀ : A₀ ∈ Chain.kSet q W)
    (_hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (_hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hr₀ : 0 ≤ r₀) (hL : 0 ≤ L)
    (hacc : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat (gaussSum q W A₀ ξ k ω))‖ ≤ r₀)
    (hlift : ‖liftSum q W A₀ ξ k ω‖ ≤ L)
    (hlt : r₀ + L < a₀) :
    Discharge.StateBounds (symMat (Chain.chain q W A₀ ξ k ω).1)
      (a₀ - (r₀ + L)) (a₀ + (r₀ + L)) := by
  refine StateInvariant.stateBounds_of_opNorm_le (symMat_isSymm _) (by positivity) hlt ?_
  have hdec : symMat (Chain.chain q W A₀ ξ k ω).1 - a₀ • (1 : Matrix (Fin n) (Fin n) ℝ)
      = symMat (gaussSum q W A₀ ξ k ω) + symMat (liftSum q W A₀ ξ k ω) := by
    rw [chain_fst_eq, symMat_add, symMat_add, hA₀m]
    abel
  rw [hdec, map_add]
  exact (norm_add_le _ _).trans
    (add_le_add hacc ((StepInputs2.opNorm_symMat_le_norm _).trans hlift))

omit [MeasurableSpace Ω] in
/-- **`StateBounds` on the wired event, with no `cV` and no factor `dim`.**  The lift enters as
`c₃ · η` with `c₃` a bound on the *accumulated* contact count — report 7 §8's H9, which the tree
already carries, not a new modelling constant. -/
theorem stateBounds_wired_count {r : ℝ} {Wacc : Ω → EuclideanSpace ℝ (UT n)} {thr : ℝ} {N : ℕ}
    {η a₀ r₀ c₃ : ℝ}
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃)
    (hcount : ∀ ω ∈ wiredGood r Wacc ξ thr N η q W A₀ r₀, ∀ k, k < N →
      ((Chain.chain q W A₀ ξ k ω).2.card : ℝ) ≤ c₃)
    (hlt : r₀ + c₃ * η < a₀) :
    ∀ k, k < N → ∀ ω ∈ wiredGood r Wacc ξ thr N η q W A₀ r₀,
      Discharge.StateBounds (symMat (Chain.chain q W A₀ ξ k ω).1)
        (a₀ - (r₀ + c₃ * η)) (a₀ + (r₀ + c₃ * η)) := by
  intro k hk ω hω
  have hstep : ∀ j, j < k → ‖gaussStep q W A₀ ξ j ω‖ ≤ η := fun j hj =>
    le_trans (Submodule.norm_starProjection_apply_le _ _) (hω.1.2 j (lt_trans hj hk))
  have hlift : ‖liftSum q W A₀ ξ k ω‖ ≤ c₃ * η := by
    refine le_trans (norm_liftSum_le_card hA₀ hq hne hη k ω hstep) ?_
    exact mul_le_mul_of_nonneg_right (hcount ω hω k hk) hη
  exact stateBounds_of_chain_count hA₀ hq hne hA₀m hr₀ (by positivity) (hω.2 k hk) hlift hlt

/-- **`hpt` on the wired event, with no `cV`** — the hand-off into
`StepInputs2.driftInputs_step_chain`. -/
theorem hpt_wired_count {r : ℝ} {Wacc : Ω → EuclideanSpace ℝ (UT n)} {thr : ℝ} {N : ℕ}
    {η a₀ r₀ c₃ δ : ℝ}
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃)
    (hcount : ∀ ω ∈ wiredGood r Wacc ξ thr N η q W A₀ r₀, ∀ k, k < N →
      ((Chain.chain q W A₀ ξ k ω).2.card : ℝ) ≤ c₃)
    (hlt : r₀ + c₃ * η < a₀)
    (hδ : η / (a₀ - (r₀ + c₃ * η)) ≤ δ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    ∀ k, k < N → ∀ ω ∈ wiredGood r Wacc ξ thr N η q W A₀ r₀,
      ChainWiring.logDet (Chain.chain q W A₀ ξ (k + 1) ω).1
        ≤ ChainWiring.logDet (Chain.chain q W A₀ ξ k ω).1
          + ⟪(Chain.freeSub q (Chain.chain q W A₀ ξ k ω).2).starProjection
              (Discharge.matToUT (symMat (Chain.chain q W A₀ ξ k ω).1)⁻¹), ξ k ω⟫
          - (1 / (2 * (a₀ + (r₀ + c₃ * η)) ^ 2 * (1 + δ) ^ 2))
            * ‖(Chain.freeSub q (Chain.chain q W A₀ ξ k ω).2).starProjection (ξ k ω)‖ ^ 2
          + ChainWiring.chainErr q W A₀ ξ k ω := by
  intro k hk ω hω
  exact Discharge.hpt_step
    (stateBounds_wired_count hA₀ hq hne hA₀m hη hr₀ hc₃ hcount hlt k hk ω hω)
    (StepInputs2.opNorm_step_le_of_stepGood hω.1.2 hk _) hδ hδ0 hδ1

end Wired

end

end Submission.L10.LiftBound

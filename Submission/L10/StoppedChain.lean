import Submission.L10.ChainSetup
import Submission.L10.StateInvariant4

/-!
# Gate L-10 (`klartag_packing`) — the stopped chain

Brief 49.  Report 47 §5–§6 named two obstructions between `ChainSetup.driftInputs_step_path` and
`ChainDrift.DriftInputs`:

* `StepInputs2.driftInputs_step_chain`'s pointwise bound `hpt` is `∀ᵐ ω ∂P` — under the **whole**
  measure — while `StateInvariant4.hpt_wired'` holds only on `wiredGood'`;
* the inverse state, its log-determinant and the chain error are unbounded off that event, so four
  integrability and four measurability hypotheses are not Gaussian moments.

Both are the same problem and have the paper's own answer (report 2 §5.5): **stop the chain at the
first exit from the good event.**  Off the good event the stopped data is frozen, so the inequality
is an equality there and the bounds of `StateInvariant4.stateBounds_wired'` hold everywhere.

## The stopping time, and which conditions it can see

`stateBounds_wired'` at step `k` consumes exactly three things, and each is measurable at time `k`:

* `‖ξ j ω‖ ≤ η` for every `j < k` (`stepGood`, at the *earlier* indices);
* `‖symMat (gaussSum … k ω)‖_op ≤ r₀` (`accGood` at `k`);
* `|C_k ω| ≤ c₃` (`countGood`'s per-step form, `card_le_of_countGood`).

`stateGood k` below is their conjunction; it is `ℱ k`-measurable, which is what makes `tauOf` a
stopping time and the stopped data adapted.  Note that the *step* condition at index `k` itself —
`‖ξ k ω‖ ≤ η`, which `hpt_wired'` also uses — is **not** `ℱ k`-measurable, and cannot be: `ξ k` is
`ℱ (k+1)`-measurable.  §4 records what that costs.

`goodEventUT`, the first component of `StepGlue.chainGood`, plays no part: `stateBounds_wired'`
never reads it.
-/


namespace Submission.L10.StoppedChain

open MeasureTheory Matrix Finset Module Submission.L10 Submission.L10.Increments
open scoped RealInnerProductSpace

/-! ## 1. The stopping time of a family of events -/

section Tau

variable {Ω : Type*}

open Classical in
/-- **The first exit before `N`.**  `tauOf G N ω` is the least `k < N` with `ω ∉ G k`, and `N` if
there is none. -/
noncomputable def tauOf (G : ℕ → Set Ω) (N : ℕ) (ω : Ω) : ℕ :=
  if h : ∃ k, k < N ∧ ω ∉ G k then Nat.find h else N

theorem tauOf_le (G : ℕ → Set Ω) (N : ℕ) (ω : Ω) : tauOf G N ω ≤ N := by
  classical
  rw [tauOf]
  split
  · rename_i h
    exact le_of_lt (Nat.find_spec h).1
  · exact le_rfl

/-- Before the stopping time every event has held. -/
theorem mem_of_lt_tauOf {G : ℕ → Set Ω} {N : ℕ} {ω : Ω} {k : ℕ} (hk : k < tauOf G N ω)
    (hkN : k < N) : ω ∈ G k := by
  classical
  by_contra hmem
  have hex : ∃ j, j < N ∧ ω ∉ G j := ⟨k, hkN, hmem⟩
  have : tauOf G N ω = Nat.find hex := by rw [tauOf, dite_eq_left hex]
  rw [this] at hk
  exact absurd (Nat.find_le ⟨hkN, hmem⟩) (not_le.2 hk)

/-- The stopping time is `N` exactly when no event failed. -/
theorem tauOf_eq_of_forall {G : ℕ → Set Ω} {N : ℕ} {ω : Ω} (h : ∀ k, k < N → ω ∈ G k) :
    tauOf G N ω = N := by
  classical
  rw [tauOf, dite_eq_right]
  rintro ⟨k, hk, hmem⟩
  exact hmem (h k hk)

theorem forall_of_tauOf_eq {G : ℕ → Set Ω} {N : ℕ} {ω : Ω} (h : tauOf G N ω = N) :
    ∀ k, k < N → ω ∈ G k := by
  intro k hk
  exact mem_of_lt_tauOf (by rw [h]; exact hk) hk

/-- `{τ ≤ k}` unfolds to a finite union of the failures at times `≤ k`. -/
theorem tauOf_le_iff {G : ℕ → Set Ω} {N : ℕ} {ω : Ω} {k : ℕ} :
    tauOf G N ω ≤ k ↔ (∃ j, j ≤ k ∧ j < N ∧ ω ∉ G j) ∨ N ≤ k := by
  classical
  constructor
  · intro hle
    by_cases hN : N ≤ k
    · exact Or.inr hN
    · left
      have hlt : tauOf G N ω < N := lt_of_le_of_lt hle (not_le.1 hN)
      have hex : ∃ j, j < N ∧ ω ∉ G j := by
        by_contra hno
        rw [tauOf, dite_eq_right hno] at hlt
        exact absurd hlt (lt_irrefl N)
      have heq : tauOf G N ω = Nat.find hex := by rw [tauOf, dite_eq_left hex]
      obtain ⟨h1, h2⟩ := Nat.find_spec hex
      exact ⟨Nat.find hex, by rw [← heq]; exact hle, h1, h2⟩
  · rintro (⟨j, hjk, hjN, hmem⟩ | hN)
    · have hex : ∃ i, i < N ∧ ω ∉ G i := ⟨j, hjN, hmem⟩
      rw [tauOf, dite_eq_left hex]
      exact le_trans (Nat.find_le ⟨hjN, hmem⟩) hjk
    · exact le_trans (tauOf_le G N ω) hN

variable [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- **`tauOf` is a stopping time** for any filtration measuring each `G k` at time `k`. -/
theorem isStoppingTime_tauOf {m0 : MeasurableSpace Ω} (ℱ : Filtration ℕ m0) {G : ℕ → Set Ω}
    (hG : ∀ k, MeasurableSet[ℱ k] (G k)) (N : ℕ) :
    IsStoppingTime ℱ (fun ω => ((tauOf G N ω : ℕ) : WithTop ℕ)) := by
  intro k
  show MeasurableSet[ℱ k] {ω | ((tauOf G N ω : ℕ) : WithTop ℕ) ≤ ((k : ℕ) : WithTop ℕ)}
  have hcast : ({ω | ((tauOf G N ω : ℕ) : WithTop ℕ) ≤ ((k : ℕ) : WithTop ℕ)} : Set Ω)
      = {ω | tauOf G N ω ≤ k} := by
    ext ω; simp
  rw [hcast]
  have hset : ({ω | tauOf G N ω ≤ k} : Set Ω)
      = (⋃ j ∈ Finset.range (k + 1), (if j < N then (G j)ᶜ else (∅ : Set Ω)))
        ∪ (if N ≤ k then (Set.univ : Set Ω) else ∅) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_iUnion, Finset.mem_range,
      Nat.lt_succ_iff]
    rw [tauOf_le_iff]
    constructor
    · rintro (⟨j, hjk, hjN, hmem⟩ | hN)
      · exact Or.inl ⟨j, hjk, by rw [ite_eq_left hjN]; exact hmem⟩
      · exact Or.inr (by rw [ite_eq_left hN]; trivial)
    · rintro (⟨j, hjk, hj⟩ | hN)
      · by_cases hjN : j < N
        · rw [ite_eq_left hjN] at hj
          exact Or.inl ⟨j, hjk, hjN, hj⟩
        · rw [ite_eq_right hjN] at hj
          exact absurd hj (Set.notMem_empty ω)
      · by_cases hNk : N ≤ k
        · exact Or.inr hNk
        · rw [ite_eq_right hNk] at hN
          exact absurd hN (Set.notMem_empty ω)
  rw [hset]
  refine MeasurableSet.union (MeasurableSet.biUnion (Finset.range (k + 1)).countable_toSet ?_) ?_
  · intro j hj
    by_cases hjN : j < N
    · rw [ite_eq_left hjN]
      exact (ℱ.mono (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) _ (hG j)).compl
    · rw [ite_eq_right hjN]; exact @MeasurableSet.empty Ω (ℱ k)
  · by_cases hNk : N ≤ k
    · rw [ite_eq_left hNk]; exact @MeasurableSet.univ Ω (ℱ k)
    · rw [ite_eq_right hNk]; exact @MeasurableSet.empty Ω (ℱ k)

end Tau


/-! ## 2. The chain's state conditions, the stopping time, and the stopped state -/

section Chain

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι] {Ω : Type*} [MeasurableSpace Ω]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

/-- **The `ℱ k`-measurable part of the good event at step `k`** — exactly the three facts
`StateInvariant4.stateBounds_wired'` consumes, and no more: the *earlier* per-step bounds, the
accumulated bound at `k`, and the contact count at `k`. -/
def stateGood (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι) (A₀ : EuclideanSpace ℝ (UT n))
    (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (η r₀ c₃ : ℝ) (k : ℕ) : Set Ω :=
  {ω | (∀ j, j < k → ‖ξ j ω‖ ≤ η) ∧
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat (StateInvariant.gaussSum q W A₀ ξ k ω))‖ ≤ r₀ ∧
    ((Chain.chain q W A₀ ξ k ω).2.card : ℝ) ≤ c₃}

omit [Countable ι] [MeasurableSpace Ω] in
/-- The chain starts inside: `gaussSum … 0 = 0` and `C₀ = ∅`. -/
theorem stateGood_zero {η r₀ c₃ : ℝ} (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃) (ω : Ω) :
    ω ∈ stateGood q W A₀ ξ η r₀ c₃ 0 := by
  refine ⟨fun j hj => absurd hj (Nat.not_lt_zero j), ?_, ?_⟩
  · have h0 : StateInvariant.gaussSum q W A₀ ξ 0 ω = 0 := by
      rw [StateInvariant.gaussSum, Finset.range_zero, Finset.sum_empty]
    rw [h0]
    have : symMat (0 : EuclideanSpace ℝ (UT n)) = 0 := by
      ext i j; rw [symMat_apply]; simp
    rw [this]
    simpa using hr₀
  · rw [Chain.chain_zero]
    simpa using hc₃

/-- **The stopping time**: the first index at which the state conditions fail.  It is a genuine
stopping time for `ℱ` — `stateGood k` is `ℱ k`-measurable — and `stateGood_zero` makes it at least
`1`, so `τ − 1` is always a *good* index.  That is what the stopped state freezes at. -/
noncomputable def tau (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι)
    (A₀ : EuclideanSpace ℝ (UT n)) (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (η r₀ c₃ : ℝ) (N : ℕ) :
    Ω → ℕ :=
  tauOf (stateGood q W A₀ ξ η r₀ c₃) N

omit [Countable ι] [MeasurableSpace Ω] in
theorem tau_le {η r₀ c₃ : ℝ} {N : ℕ} (ω : Ω) : tau q W A₀ ξ η r₀ c₃ N ω ≤ N :=
  tauOf_le _ N ω

omit [Countable ι] [MeasurableSpace Ω] in
/-- The chain never stops at `0`. -/
theorem one_le_tau {η r₀ c₃ : ℝ} {N : ℕ} (hN : 1 ≤ N) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃) (ω : Ω) :
    1 ≤ tau q W A₀ ξ η r₀ c₃ N ω := by
  rcases Nat.eq_zero_or_pos (tau q W A₀ ξ η r₀ c₃ N ω) with h0 | hpos
  · exfalso
    have hle : tau q W A₀ ξ η r₀ c₃ N ω ≤ 0 := le_of_eq h0
    rcases tauOf_le_iff.1 hle with ⟨j, hj0, hjN, hmem⟩ | hN0
    · have hj : j = 0 := by omega
      subst hj
      exact hmem (stateGood_zero hr₀ hc₃ ω)
    · omega
  · exact hpos

omit [Countable ι] [MeasurableSpace Ω] in
/-- **Every index strictly below the stopping time is good.** -/
theorem stateGood_of_lt_tau {η r₀ c₃ : ℝ} {N : ℕ} {ω : Ω} {j : ℕ}
    (hj : j < tau q W A₀ ξ η r₀ c₃ N ω) :
    ω ∈ stateGood q W A₀ ξ η r₀ c₃ j :=
  mem_of_lt_tauOf (N := N) hj (lt_of_lt_of_le hj (tau_le ω))

/-- **`wiredGood' ⊆ {τ = N}`.**  On the event the chain is run on, nothing ever stops. -/
theorem tau_eq_of_wiredGood' {r : ℝ} {Wacc : Ω → EuclideanSpace ℝ (UT n)} {thr : ℝ} {N : ℕ}
    {η r₀ c₃ : ℝ} {ω : Ω}
    (hω : ω ∈ StateInvariant4.wiredGood' r Wacc ξ thr N η q W A₀ r₀ c₃) :
    tau q W A₀ ξ η r₀ c₃ N ω = N := by
  refine tauOf_eq_of_forall (fun k hk => ?_)
  have hstep : ∀ i, i < N → ‖ξ i ω‖ ≤ η := hω.1.1.2
  have hacc : ∀ i, i < N →
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat (StateInvariant.gaussSum q W A₀ ξ i ω))‖ ≤ r₀ :=
    hω.1.2
  exact ⟨fun j hj => hstep j (by omega), hacc k hk,
    StateInvariant4.card_le_of_countGood (k := k) hω.2 (le_of_lt hk)⟩

/-- **The stopped state** `A^τ_k := A_{min k (τ−1)}`: frozen at the last index the state conditions
covered.  `one_le_tau` makes `τ − 1` well defined and good. -/
noncomputable def stoppedState (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι)
    (A₀ : EuclideanSpace ℝ (UT n)) (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (η r₀ c₃ : ℝ) (N k : ℕ)
    (ω : Ω) : EuclideanSpace ℝ (UT n) :=
  (Chain.chain q W A₀ ξ (min k (tau q W A₀ ξ η r₀ c₃ N ω - 1)) ω).1

omit [Countable ι] [MeasurableSpace Ω] in
/-- **On `{τ = N}` the stopped chain is the chain**, for every step of the horizon `N − 1` — in
particular on `wiredGood'`. -/
theorem stoppedState_eq {η r₀ c₃ : ℝ} {N k : ℕ} {ω : Ω}
    (hτ : tau q W A₀ ξ η r₀ c₃ N ω = N) (hk : k ≤ N - 1) :
    stoppedState q W A₀ ξ η r₀ c₃ N k ω = (Chain.chain q W A₀ ξ k ω).1 := by
  rw [stoppedState, hτ, min_eq_left hk]

omit [Countable ι] [MeasurableSpace Ω] in
/-- **The bounds hold for the stopped state everywhere** — no good event and no a.e.  This is what
makes the inverse state, its log-determinant and the chain error bounded, and so the eight
integrability and measurability hypotheses of the drift theorem reachable. -/
theorem stateBounds_stopped {η a₀ r₀ c₃ : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃)
    (hlt : r₀ + c₃ * η < a₀) (k : ℕ) (ω : Ω) :
    Discharge.StateBounds (symMat (stoppedState q W A₀ ξ η r₀ c₃ N k ω))
      (a₀ - (r₀ + c₃ * η)) (a₀ + (r₀ + c₃ * η)) := by
  have hpos := one_le_tau (q := q) (W := W) (A₀ := A₀) (ξ := ξ) (η := η) (r₀ := r₀) (c₃ := c₃)
    hN hr₀ hc₃ ω
  have hjt : min k (tau q W A₀ ξ η r₀ c₃ N ω - 1) < tau q W A₀ ξ η r₀ c₃ N ω := by
    have := min_le_right k (tau q W A₀ ξ η r₀ c₃ N ω - 1)
    omega
  obtain ⟨hstepj, haccj, hcntj⟩ := stateGood_of_lt_tau (q := q) (W := W) (A₀ := A₀) (ξ := ξ)
    (η := η) (r₀ := r₀) (c₃ := c₃) (N := N) hjt
  have hstep : ∀ i, i < min k (tau q W A₀ ξ η r₀ c₃ N ω - 1) →
      ‖StateInvariant.gaussStep q W A₀ ξ i ω‖ ≤ η := fun i hi =>
    le_trans (Submodule.norm_starProjection_apply_le _ _) (hstepj i hi)
  have hlift : ‖StateInvariant.liftSum q W A₀ ξ
      (min k (tau q W A₀ ξ η r₀ c₃ N ω - 1)) ω‖ ≤ c₃ * η := by
    refine le_trans (LiftBound.norm_liftSum_le_card hA₀ hq hne hη _ ω hstep) ?_
    exact mul_le_mul_of_nonneg_right hcntj hη
  exact LiftBound.stateBounds_of_chain_count hA₀ hq hne hA₀m hr₀ (by positivity) haccj hlift hlt


omit [Countable ι] [MeasurableSpace Ω] in
/-- **`τ` is a stopping time** for any filtration that measures the state conditions at their own
index — which `ChainSetup.filtration` does, since `Chain.measurable_chain` makes the chain adapted
and `ξ j` is `ℱ (j+1)`-measurable for `j < k`. -/
theorem isStoppingTime_tau {m0 : MeasurableSpace Ω} (ℱ : Filtration ℕ m0) {η r₀ c₃ : ℝ}
    (hG : ∀ k, MeasurableSet[ℱ k] (stateGood q W A₀ ξ η r₀ c₃ k)) (N : ℕ) :
    IsStoppingTime ℱ (fun ω => ((tau q W A₀ ξ η r₀ c₃ N ω : ℕ) : WithTop ℕ)) :=
  isStoppingTime_tauOf ℱ hG N

/-- The stopped state agrees with the chain on `wiredGood'`, for every step of the horizon. -/
theorem stoppedState_eq_of_wiredGood' {r : ℝ} {Wacc : Ω → EuclideanSpace ℝ (UT n)} {thr : ℝ}
    {N k : ℕ} {η r₀ c₃ : ℝ} {ω : Ω}
    (hω : ω ∈ StateInvariant4.wiredGood' r Wacc ξ thr N η q W A₀ r₀ c₃) (hk : k ≤ N - 1) :
    stoppedState q W A₀ ξ η r₀ c₃ N k ω = (Chain.chain q W A₀ ξ k ω).1 :=
  stoppedState_eq (tau_eq_of_wiredGood' hω) hk


end Chain

end Submission.L10.StoppedChain

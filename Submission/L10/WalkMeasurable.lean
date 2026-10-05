/-
Gate L-10 (`klartag_packing`), brief 48.

**Measurability of the chain's scalar walk.**

Report 45 left this step unwritten: the attempt hit the `MeasurableSpace (Finset ι)` instance
diamond and a defeq timeout.  Both recorded fixes apply.

* `Chain.measurable_chain_fst` already exports `A_k`'s measurability with the discrete σ-algebra on
  `Finset ι` declared **locally**, so the statement mentions only `E` and `Ω` — report 34 §6.  No
  σ-algebra on `Finset ι` is needed here at all.
* Where the active set genuinely enters — the pure walk's increment reads both `C_k` and `ξ_k` —
  the countable partition is written by hand over `W.powerset`, exactly as
  `ChainWiring.measurable_of_active` does, with `ChainWiring.measurableSet_active_eq` for the
  fibres.
* Every composition is written into a `have`'s type rather than left to the elaborator — report
  41 §1.
-/
import Submission.L10.WalkTelescope
import Submission.L10.ChainWiring

namespace Submission.L10

open MeasureTheory Set Real Submission.L10.Chain Submission.L10.Increments
open scoped RealInnerProductSpace

section Measurable

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι]
variable {Ω : Type*} [MeasurableSpace Ω]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
variable {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

/-- **The lifted constraint walk `⟪A_k, q x⟫` is measurable.** -/
theorem measurable_walk (hξ : ∀ k, Measurable (ξ k)) (x : ι) (k : ℕ) :
    Measurable fun ω => ⟪(chain q W A₀ ξ k ω).1, q x⟫ := by
  have hinner : Measurable fun v : EuclideanSpace ℝ (UT n) => ⟪v, q x⟫ :=
    (continuous_inner.comp (continuous_id.prodMk continuous_const)).measurable
  have hcomp : Measurable ((fun v : EuclideanSpace ℝ (UT n) => ⟪v, q x⟫)
      ∘ fun ω => (chain q W A₀ ξ k ω).1) :=
    hinner.comp (measurable_chain_fst hξ k)
  exact hcomp

/-- **A statistic that reads both the active set and the increment is measurable.**  Report 34 §6's
partition, widened from `f (C_k ω)` to `f (C_k ω) (ξ_k ω)`. -/
theorem measurable_of_active_and_inc (hξ : ∀ k, Measurable (ξ k)) (k : ℕ)
    (f : Finset ι → EuclideanSpace ℝ (UT n) → ℝ) (hf : ∀ c : Finset ι, Measurable (f c)) :
    Measurable fun ω => f (chain q W A₀ ξ k ω).2 (ξ k ω) := by
  classical
  have hrep : (fun ω => f (chain q W A₀ ξ k ω).2 (ξ k ω))
      = fun ω => ∑ c ∈ W.powerset,
          if (chain q W A₀ ξ k ω).2 = c then f c (ξ k ω) else 0 := by
    funext ω
    rw [Finset.sum_ite_eq W.powerset (chain q W A₀ ξ k ω).2 (fun c => f c (ξ k ω)),
      ite_eq_left (Finset.mem_powerset.2 (chain_snd_subset_window k ω))]
  rw [hrep]
  refine Finset.measurable_sum _ fun c _ => ?_
  have hbranch : Measurable fun ω => f c (ξ k ω) := (hf c).comp (hξ k)
  exact Measurable.ite (ChainWiring.measurableSet_active_eq hξ k c) hbranch measurable_const

/-- **The pure walk is measurable** — the increment reads the active set through the projection. -/
theorem measurable_pureWalk (hξ : ∀ k, Measurable (ξ k)) (x : ι) (k : ℕ) :
    Measurable (pureWalk q W A₀ ξ x k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    show Measurable fun ω => pureWalk q W A₀ ξ x k ω
      + ⟪(freeSub q (chain q W A₀ ξ k ω).2).starProjection (ξ k ω), q x⟫
    refine ih.add ?_
    refine measurable_of_active_and_inc hξ k
      (fun c v => ⟪(freeSub q c).starProjection v, q x⟫) fun c => ?_
    have hcont : Continuous fun v : EuclideanSpace ℝ (UT n) =>
        ⟪(freeSub q c).starProjection v, q x⟫ :=
      continuous_inner.comp ((freeSub q c).starProjection.continuous.prodMk continuous_const)
    exact hcont.measurable

/-- **`WalkTelescope.hprop_of_hincl`'s `hM`.** -/
theorem measurable_constraintM (hξ : ∀ k, Measurable (ξ k)) (x : ι) (k : ℕ) :
    Measurable (constraintM q W A₀ ξ x k) :=
  (measurable_pureWalk hξ x k).sub measurable_const

/-! ### The adapted version -/

omit [Countable ι] [MeasurableSpace Ω] in
/-- The chain reads only the increments before time `k`. -/
theorem chain_eq_of_eq {Ω' : Type*} (ξ' : ℕ → Ω' → EuclideanSpace ℝ (UT n))
    (ω : Ω) (ω' : Ω') (k : ℕ) (h : ∀ j < k, ξ j ω = ξ' j ω') :
    chain q W A₀ ξ k ω = chain q W A₀ ξ' k ω' := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk : ∀ j < k, ξ j ω = ξ' j ω' := fun j hj => h j (Nat.lt_succ_of_lt hj)
    rw [chain_succ, chain_succ, ih hk, h k (Nat.lt_succ_self k)]

/-- The walk as a function of the past alone. -/
noncomputable def walkOfPast (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι)
    (A₀ : EuclideanSpace ℝ (UT n)) (x : ι) (k : ℕ) (p : ℕ → EuclideanSpace ℝ (UT n)) : ℝ :=
  ⟪(chain q W A₀ (fun j (p' : ℕ → EuclideanSpace ℝ (UT n)) => p' j) k p).1, q x⟫

theorem measurable_walkOfPast (x : ι) (k : ℕ) : Measurable (walkOfPast q W A₀ x k) :=
  measurable_walk (ξ := fun j (p : ℕ → EuclideanSpace ℝ (UT n)) => p j)
    (fun j => measurable_pi_apply j) x k

omit [Countable ι] [MeasurableSpace Ω] in
/-- **Adaptedness.**  `⟪A_k, q x⟫` factors through `PaddingMap.pastOf ξ k`, so it is measurable for
the σ-algebra generated by the first `k` increments — the filtration `StateInvariant4` works
against. -/
theorem walk_eq_walkOfPast (x : ι) (k : ℕ) (ω : Ω) :
    ⟪(chain q W A₀ ξ k ω).1, q x⟫ = walkOfPast q W A₀ x k (pastOf ξ k ω) := by
  unfold walkOfPast
  rw [chain_eq_of_eq (q := q) (W := W) (A₀ := A₀)
    (fun j (p' : ℕ → EuclideanSpace ℝ (UT n)) => p' j) ω (pastOf ξ k ω) k
    (fun j hj => (ite_eq_left hj).symm)]

theorem measurable_walk_comap (_hξ : ∀ j, Measurable (ξ j)) (x : ι) (k : ℕ) :
    Measurable[MeasurableSpace.comap (pastOf ξ k) inferInstance]
      fun ω => ⟪(chain q W A₀ ξ k ω).1, q x⟫ := by
  have hfun : (fun ω => ⟪(chain q W A₀ ξ k ω).1, q x⟫)
      = (walkOfPast q W A₀ x k) ∘ (pastOf ξ k) := by
    funext ω; exact walk_eq_walkOfPast x k ω
  rw [hfun]
  exact (measurable_walkOfPast x k).comp (Measurable.of_comap_le le_rfl)

end Measurable

end Submission.L10

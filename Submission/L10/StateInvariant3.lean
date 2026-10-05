import Submission.L10.StateInvariant2

/-!
# Gate L-10 (`klartag_packing`), brief 36 — (B)'s remainder

Report 34 §5 listed four items. Three are here: `reflection_congr` (the `subst` fix for the
"motive is not type correct" on `Submodule.reflection`'s instance argument), `measurable_past`,
`indepFun_past`, and the first half-law `map_sum_xi`.

**`map_sum_reflStep` (the second half-law) is not here**, and the obstruction is sharp: the bridge
`reflStep q W A₀ ξ k ω = reflOf q (chainU q W A₀ k (past ξ k ω)).2 (ξ k ω)` — the statement that
the frozen reflection is a function of the past — cannot be elaborated. Unfolding
`StateInvariant.reflStep` to its body against a freshly synthesised
`Submodule.HasOrthogonalProjection (Chain.freeSub q …)` runs past **1,000,000 heartbeats**
(3 min 22 s), by `show`, by `rw`, and by term-mode `congrArg` alike. `reflection_congr` itself is
fine; it is the unfolding of `reflStep` that is not. The fix is upstream, not here: `reflStep`
must be *defined* through `chainU`/`past` so that the bridge is `rfl`, and
`Submission/L10/StateInvariant.lean` is reported and frozen (rule 5). See the report, §3.
-/

set_option linter.unusedSectionVars false

namespace Submission.L10.StateInvariant3

open MeasureTheory ProbabilityTheory Matrix Finset Module
open scoped ENNReal NNReal RealInnerProductSpace
open Submission.L10 Submission.L10.Increments Submission.L10.StateInvariant
open Submission.L10.StateInvariant2

noncomputable section

/-- `Submodule.reflection` carries a `HasOrthogonalProjection` instance argument depending on the
subspace, so `rw` on the subspace fails ("motive is not type correct").  `subst` does not. -/
theorem reflection_congr {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K L : Submodule ℝ E} [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (h : K = L) (x : E) : K.reflection x = L.reflection x := by
  subst h; rfl

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

theorem measurable_past (hξ : ∀ j, Measurable (ξ j)) (k : ℕ) : Measurable (past ξ k) := by
  refine Measurable.of_eval fun j => ?_
  show Measurable fun ω => if j < k then ξ j ω else (0 : EuclideanSpace ℝ (UT n))
  by_cases h : j < k
  · simp only [ite_eq_left h]; exact hξ j
  · simp only [ite_eq_right h]; exact measurable_const

theorem indepFun_past (hξ : ∀ j, Measurable (ξ j)) (hindep : iIndepFun ξ P) (k : ℕ) :
    IndepFun (past ξ k) (ξ k) P := by
  classical
  have hdisj : Disjoint (Finset.range k) ({k} : Finset ℕ) := by
    simp [Finset.disjoint_singleton_right]
  have hbase := hindep.indepFun_finset (Finset.range k) {k} hdisj (fun j => hξ j)
  have hf : Measurable fun u : (↥(Finset.range k) → EuclideanSpace ℝ (UT n)) =>
      (fun j => if h : j < k then u ⟨j, Finset.mem_range.2 h⟩ else 0 :
        ℕ → EuclideanSpace ℝ (UT n)) := by
    refine Measurable.of_eval fun j => ?_
    by_cases h : j < k
    · show Measurable fun u : (↥(Finset.range k) → EuclideanSpace ℝ (UT n)) =>
        if h' : j < k then u ⟨j, Finset.mem_range.2 h'⟩ else 0
      simp only [dite_eq_left h]
      exact measurable_pi_apply (⟨j, Finset.mem_range.2 h⟩ : ↥(Finset.range k))
    · show Measurable fun u : (↥(Finset.range k) → EuclideanSpace ℝ (UT n)) =>
        if h' : j < k then u ⟨j, Finset.mem_range.2 h'⟩ else 0
      simp only [dite_eq_right h]
      exact measurable_const
  have hg : Measurable fun u : (↥({k} : Finset ℕ) → EuclideanSpace ℝ (UT n)) =>
      u ⟨k, Finset.mem_singleton_self k⟩ := measurable_pi_apply _
  have hcomp := hbase.comp hf hg
  have e1 : ((fun u : (↥(Finset.range k) → EuclideanSpace ℝ (UT n)) =>
        (fun j => if h : j < k then u ⟨j, Finset.mem_range.2 h⟩ else 0 :
          ℕ → EuclideanSpace ℝ (UT n)))
      ∘ fun (ω : Ω) (i : ↥(Finset.range k)) => ξ i ω) = past ξ k := by
    funext ω j
    show (if h : j < k then ξ j ω else 0) = (past ξ k ω) j
    by_cases h : j < k
    · rw [dite_eq_left h]; simp [past, h]
    · rw [dite_eq_right h]; simp [past, h]
  have e2 : ((fun u : (↥({k} : Finset ℕ) → EuclideanSpace ℝ (UT n)) =>
        u ⟨k, Finset.mem_singleton_self k⟩)
      ∘ fun (ω : Ω) (i : ↥({k} : Finset ℕ)) => ξ i ω) = ξ k := rfl
  rw [e1, e2] at hcomp
  exact hcomp

/-- **(B1)** `Σ_{j<k} ξ_j ~ N(0, k c² · Id)`. -/
theorem map_sum_xi {c : ℝ} (hc : 0 ≤ c) (hξ : ∀ j, Measurable (ξ j))
    (hindep : iIndepFun ξ P) (hlaw : ∀ j, P.map (ξ j) = scaled c (EuclideanSpace ℝ (UT n)))
    (k : ℕ) :
    P.map (fun ω => ∑ j ∈ Finset.range k, ξ j ω)
      = scaled (Real.sqrt k * c) (EuclideanSpace ℝ (UT n)) :=
  map_sum_scaled hc hξ hlaw (fun m => by
    have h := hindep.indepFun_sum_range_succ hξ m
    have e : (∑ j ∈ Finset.range m, ξ j) = fun ω => ∑ j ∈ Finset.range m, ξ j ω := by
      funext ω; rw [Finset.sum_apply]
    rwa [e] at h) k


end

end Submission.L10.StateInvariant3

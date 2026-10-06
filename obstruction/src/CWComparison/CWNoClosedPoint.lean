/-
Copyright (c) 2026. Released under Apache 2.0.
Checks a genuine issue in the exact protected classical CW predicate: its
weak-topology condition uses ambient closed cell intersections and it assumes
no separation axiom. The zero-cell construction below adapts Mathlib's
CWComplex.OfDiscreteClosed by Jiazhen Xia, Elliot Dean Young and Joël Riou,
Apache-2.0. No protected definition is changed.
-/
import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.Order

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Metric Set Function

namespace CWComparison

/-- Any space with no closed singleton satisfies the EXACT original classical
CW predicate, using only zero-cells. This does not add a separation premise. -/
@[instance_reducible]
def cwComplexOfNoClosedSingleton {X : Type} [TopologicalSpace X]
    (hX : ∀ x : X, ¬ IsClosed ({x} : Set X)) :
    Topology.CWComplex (univ : Set X) where
  cell n := match n with
    | 0 => X
    | (_ + 1) => PEmpty
  map n i := match n with
    | 0 => PartialEquiv.single ![] i
    | (_ + 1) => i.elim
  source_eq n i := match n with
    | 0 => by simp [ball, Matrix.empty_eq, eq_univ_iff_forall]
    | (_ + 1) => i.elim
  continuousOn n i := match n with
    | 0 => continuousOn_const
    | (_ + 1) => i.elim
  continuousOn_symm n i := match n with
    | 0 => continuousOn_const
    | (_ + 1) => i.elim
  pairwiseDisjoint' := by
    simp_rw [PairwiseDisjoint, Set.Pairwise, Function.onFun]
    rintro ⟨_|n, j⟩ _ ⟨_|m, i⟩ _ ne
    · simp_all
    · exact i.elim
    · exact j.elim
    · exact i.elim
  mapsTo' n i := match n with
    | 0 => by simp [Matrix.zero_empty, sphere_eq_empty_of_subsingleton]
    | (_ + 1) => i.elim
  closed' A _ hA := by
    have hEmpty : A = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      apply hX x
      have hxA := hA 0 x
      simpa [hx, inter_singleton_of_mem hx] using hxA
    rw [hEmpty]
    exact isClosed_empty
  union' := by
    apply subset_antisymm (subset_univ _)
    intro x _
    simp only [mem_iUnion, mem_image, mem_closedBall, dist_zero_right]
    refine ⟨0, x, 0, ?_, ?_⟩
    · rw [norm_zero]
      exact zero_le_one
    · rfl

/-- The indiscrete double is a nontrivial space with no closed point. -/
abbrev indiscreteDouble := WithTopology Bool ⊤

theorem indiscreteDouble_not_isClosed_singleton (b : indiscreteDouble) :
    ¬ IsClosed ({b} : Set indiscreteDouble) := by
  rw [IndiscreteTopology.isClosed_iff]
  intro h
  rcases h with h | h
  · have : b ∈ (∅ : Set indiscreteDouble) := by rw [← h]; exact mem_singleton b
    exact this
  · have : (Set.univ : Set indiscreteDouble).Subsingleton := by rw [← h]; exact subsingleton_singleton
    have hf := this (mem_univ (WithTopology.toTopology ⊤ false))
      (mem_univ (WithTopology.toTopology ⊤ true))
    exact Bool.false_ne_true (WithTopology.toTopology_injective ⊤ hf)

end CWComparison

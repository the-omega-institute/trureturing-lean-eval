/-
Copyright (c) 2026. Released under Apache 2.0.
Initial-object contractions for the actual horizontal fibers in the singular
category-of-simplices replacement. Mathlib's all-degree extra-degeneracy
contraction is reused (Joël Riou, Apache-2.0).
-/
import Mathlib.AlgebraicTopology.ExtraDegeneracy
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.CategoryTheory.Comma.Over.Basic

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits Opposite AlgebraicTopology
open scoped Simplicial

namespace CWComparison

private theorem ordinal_functor {m n : SimplexCategory} (f : m ⟶ n) :
    (SimplexCategory.toCat.map f).toFunctor = f.toOrderHom.monotone.functor := rfl

private theorem ordinal_delta {n : ℕ} (i : Fin (n + 2)) :
    (SimplexCategory.toCat.map (SimplexCategory.δ i)).toFunctor =
      i.succAboveOrderEmb.monotone.functor := rfl

private theorem ordinal_sigma {n : ℕ} (i : Fin (n + 1)) :
    (SimplexCategory.toCat.map (SimplexCategory.σ i)).toFunctor =
      i.predAboveOrderHom.monotone.functor := rfl

private theorem delta_succ_mk {n : ℕ} (i : Fin (n + 2)) (j : ℕ) (hj : j < n + 1) :
    i.succ.succAbove (⟨j + 1, by omega⟩ : Fin (n + 2)) =
      (i.succAbove (⟨j, hj⟩ : Fin (n + 1))).succ :=
  Fin.succ_succAbove_succ i ⟨j, hj⟩

private theorem sigma_succ_mk {n : ℕ} (i : Fin (n + 1)) (j : ℕ) (hj : j < n + 2) :
    i.succ.predAbove (⟨j + 1, by omega⟩ : Fin (n + 3)) =
      (i.predAbove (⟨j, hj⟩ : Fin (n + 2))).succ :=
  Fin.succ_predAbove_succ i ⟨j, hj⟩

private theorem precomp_map_transport {C : Type} [SmallCategory C]
    {n : ℕ} (c : ComposableArrows C n) {X : C} (f : X ⟶ c.left)
    {a b a' b' : Fin (n + 2)} (ha : a = a') (hb : b = b') (h : a ≤ b) :
    ComposableArrows.Precomp.map c f a b h =
      eqToHom (congrArg (ComposableArrows.Precomp.obj c X) ha) ≫
        ComposableArrows.Precomp.map c f a' b' (by simpa [← ha, ← hb] using h) ≫
          eqToHom (congrArg (ComposableArrows.Precomp.obj c X) hb).symm := by
  subst a'
  subst b'
  simp

private theorem ordinal_obj {m n : SimplexCategory} (f : m ⟶ n)
    (j : Fin (m.len + 1)) :
    (SimplexCategory.toCat.map f).toFunctor.obj j = f.toOrderHom j := rfl

private theorem ordinal_map {m n : SimplexCategory} (f : m ⟶ n)
    {j k : Fin (m.len + 1)} (h : j ≤ k) :
    (SimplexCategory.toCat.map f).toFunctor.map (homOfLE h : j ⟶ k) =
      (homOfLE (f.toOrderHom.monotone h) : f.toOrderHom j ⟶ f.toOrderHom k) := rfl

/-- The actual nerve augmentation to a point. -/
def initialNerveAugmented (C : Type) [SmallCategory C] :
    SimplicialObject.Augmented (Type) where
  left := nerve C
  right := PUnit
  hom := { app := fun _ => ↾fun _ => PUnit.unit }

/-- Prepending the actual initial object is a genuine extra degeneracy. -/
def initialNerveExtraDegeneracy (C : Type) [SmallCategory C] [HasInitial C] :
    SimplicialObject.Augmented.ExtraDegeneracy (initialNerveAugmented C) where
  s' := ↾fun _ => ComposableArrows.mk₀ (⊥_ C)
  s n := ↾fun c => c.precomp (initial.to c.left)
  s'_comp_ε := by ext x; rfl
  s₀_comp_δ₁ := by
    ext c
    exact ComposableArrows.ext₀ rfl
  s_comp_δ₀ n := by
    ext c
    exact c.precomp_δ₀ (initial.to c.left)
  s_comp_δ n i := by
    ext c
    change ComposableArrows C (n + 1) at c
    refine ComposableArrows.ext (fun j => ?_) (fun j hj => ?_)
    ·
      change ComposableArrows.Precomp.obj c (⊥_ C) (i.succ.succAbove j) =
        ComposableArrows.Precomp.obj ((nerve C).δ i c) (⊥_ C) j
      cases j using Fin.cases <;>
        simp [ComposableArrows.Precomp.obj, nerve.δ_obj] <;> rfl
    ·
      cases j with
      | zero =>
        simp [initialNerveAugmented, nerve, SimplicialObject.δ,
          ComposableArrows.map', ComposableArrows.precomp,
          ordinal_obj, ordinal_map, SimplexCategory.δ,
          ComposableArrows.Precomp.map]
        apply initialIsInitial.hom_ext
      | succ j =>
        simp only [unop_op, SimplexCategory.len_mk] at hj
        change ComposableArrows.Precomp.map c (initial.to c.left)
          (i.succ.succAbove ⟨j + 1, by omega⟩)
          (i.succ.succAbove ⟨j + 1 + 1, by omega⟩) _ = _
        rw [precomp_map_transport c (initial.to c.left)
          (delta_succ_mk i j (by omega)) (delta_succ_mk i (j + 1) (by omega))]
        simp [initialNerveAugmented, SimplicialObject.δ, nerve,
          ComposableArrows.Precomp.map, ComposableArrows.map'] <;> rfl
  s_comp_σ n i := by
    ext c
    change ComposableArrows C n at c
    refine ComposableArrows.ext (fun j => ?_) (fun j hj => ?_)
    ·
      change ComposableArrows.Precomp.obj c (⊥_ C) (i.succ.predAbove j) =
        ComposableArrows.Precomp.obj ((nerve C).σ i c) (⊥_ C) j
      cases j using Fin.cases <;>
        simp [ComposableArrows.Precomp.obj, nerve.σ_obj] <;> rfl
    ·
      cases j with
      | zero =>
        simp [initialNerveAugmented, nerve, SimplicialObject.σ,
          ComposableArrows.map', ComposableArrows.precomp,
          ordinal_obj, ordinal_map, SimplexCategory.σ,
          ComposableArrows.Precomp.map]
        apply initialIsInitial.hom_ext
      | succ j =>
        simp only [unop_op, SimplexCategory.len_mk] at hj
        change ComposableArrows.Precomp.map c (initial.to c.left)
          (i.succ.predAbove ⟨j + 1, by omega⟩)
          (i.succ.predAbove ⟨j + 1 + 1, by omega⟩) _ = _
        rw [precomp_map_transport c (initial.to c.left)
          (sigma_succ_mk i j (by omega)) (sigma_succ_mk i (j + 1) (by omega))]
        simp [initialNerveAugmented, SimplicialObject.σ, nerve,
          ComposableArrows.Precomp.map, ComposableArrows.map'] <;> rfl

end CWComparison

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in src/licenses/LICENSE.LeanCondensed.
-/
import CWSolid.ComplexAdjunction
import Mathlib.Algebra.Homology.DerivedCategory.KProjective

noncomputable section
open CategoryTheory Limits

namespace CWComparison

/-- Transport a bijection on morphisms through a commutative square of functors. -/
theorem map_bijective_of_square
    {C C' D D' : Type*} [Category* C] [Category* C'] [Category* D] [Category* D']
    (A : C ⥤ D) (B : C' ⥤ D') (G : C ⥤ C') (H : D ⥤ D')
    (e : A ⋙ H ≅ G ⋙ B) (X Y : C)
    (hA : Function.Bijective (A.map : (X ⟶ Y) → _))
    (hG : Function.Bijective (G.map : (X ⟶ Y) → _))
    (hB : Function.Bijective (B.map : (G.obj X ⟶ G.obj Y) → _)) :
    Function.Bijective (H.map : (A.obj X ⟶ A.obj Y) → _) := by
  let c := Iso.homCongr (e.app X) (e.app Y)
  have hc : ∀ f : X ⟶ Y, c (H.map (A.map f)) = B.map (G.map f) := by
    intro f
    dsimp [c, Iso.homCongr]
    rw [show H.map (A.map f) ≫ e.hom.app Y = e.hom.app X ≫ B.map (G.map f) from
      e.hom.naturality f]
    simp
  constructor
  · intro f g hfg
    obtain ⟨f', rfl⟩ := hA.surjective f
    obtain ⟨g', rfl⟩ := hA.surjective g
    have h := congrArg c hfg
    rw [hc, hc] at h
    exact congrArg A.map (hG.injective (hB.injective h))
  · intro f
    obtain ⟨g, hg⟩ := hB.surjective (c f)
    obtain ⟨g', rfl⟩ := hG.surjective g
    refine ⟨A.map g', c.injective ?_⟩
    rw [hc, hg]

/-- An exact fully faithful inclusion remains fully faithful on morphisms
from a complex which is K-projective on both sides. The target can be any
object of the unbounded derived category. -/
theorem exactDerived_map_bijective_of_isKProjective
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [F.Full] [F.Faithful]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : CochainComplex C ℤ) [K.IsKProjective]
    [CochainComplex.IsKProjective ((F.mapHomologicalComplex (.up ℤ)).obj K)]
    (Y : DerivedCategory C) :
    Function.Bijective (F.mapDerivedCategory.map :
      (DerivedCategory.Q.obj K ⟶ Y) → _) := by
  let L := DerivedCategory.Qh.objPreimage Y
  let eK := (DerivedCategory.quotientCompQhIso C).app K
  let eY := DerivedCategory.Qh.objObjPreimageIso Y
  have hb := map_bijective_of_square
    (DerivedCategory.Qh (C := C)) (DerivedCategory.Qh (C := D))
    (F.mapHomotopyCategory (.up ℤ)) F.mapDerivedCategory
    F.mapDerivedCategoryFactorsh
    ((HomotopyCategory.quotient C (.up ℤ)).obj K) L
    (CochainComplex.IsKProjective.Qh_map_bijective K L)
    ⟨Functor.map_injective _, Functor.map_surjective _⟩
    (CochainComplex.IsKProjective.Qh_map_bijective
      ((F.mapHomologicalComplex (.up ℤ)).obj K)
      ((F.mapHomotopyCategory (.up ℤ)).obj L))
  let a := Iso.homCongr eK eY
  let b := Iso.homCongr (F.mapDerivedCategory.mapIso eK)
    (F.mapDerivedCategory.mapIso eY)
  have hc : ∀ f, F.mapDerivedCategory.map (a f) = b (F.mapDerivedCategory.map f) := by
    intro f
    simp [a, b, Iso.homCongr]
  constructor
  · intro f g hfg
    obtain ⟨f', rfl⟩ := a.surjective f
    obtain ⟨g', rfl⟩ := a.surjective g
    rw [hc, hc] at hfg
    exact congrArg a (hb.injective (b.injective hfg))
  · intro f
    obtain ⟨g, hg⟩ := hb.surjective (b.symm f)
    refine ⟨a g, ?_⟩
    rw [hc, hg]
    exact b.apply_symm_apply f

/-- A right adjoint is fully faithful on morphisms from `X` precisely when
its counit at `X` is an isomorphism. This local criterion does not assert
full faithfulness of the right adjoint on arbitrary derived objects. -/
theorem counit_isIso_of_map_bijective
    {C D : Type*} [Category* C] [Category* D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (X : D)
    (h : ∀ Y : D, Function.Bijective (R.map : (X ⟶ Y) → _)) :
    IsIso (adj.counit.app X) := by
  have hp : ∀ Y : D, Function.Bijective
      (fun f : X ⟶ Y => adj.counit.app X ≫ f) := by
    intro Y
    have he : ∀ f : X ⟶ Y,
        (adj.homEquiv (R.obj X) Y) (adj.counit.app X ≫ f) = R.map f := by
      intro f
      simp [Adjunction.homEquiv_unit]
    constructor
    · intro f g hfg
      apply (h Y).injective
      simpa only [he] using congrArg (adj.homEquiv (R.obj X) Y) hfg
    · intro f
      obtain ⟨g, hg⟩ := (h Y).surjective ((adj.homEquiv (R.obj X) Y) f)
      refine ⟨g, (adj.homEquiv (R.obj X) Y).injective ?_⟩
      rw [he, hg]
  obtain ⟨i, hi⟩ := (hp (L.obj (R.obj X))).surjective (𝟙 _)
  refine ⟨⟨i, hi, ?_⟩⟩
  apply (hp X).injective
  simp [← Category.assoc, hi]

end CWComparison

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in src/licenses/LICENSE.LeanCondensed.
-/
import CWComparison.FrozenDerivedAdjunction
import CWComparison.DerivedMap

noncomputable section
open CategoryTheory Limits

namespace CWComparison

/-- Transport a bijective endomorphism along an equivalence. -/
theorem bijective_conjugate {α β : Type*} (e : α ≃ β)
    (f : α → α) (g : β → β) (h : ∀ x, e (f x) = g (e x))
    (hf : Function.Bijective f) : Function.Bijective g := by
  constructor
  · intro x y hxy
    obtain ⟨x', rfl⟩ := e.surjective x
    obtain ⟨y', rfl⟩ := e.surjective y
    exact congrArg e (hf.injective (e.injective (by simpa only [h] using hxy)))
  · intro y
    obtain ⟨x, hx⟩ := hf.surjective (e.symm y)
    refine ⟨e x, ?_⟩
    rw [← h, hx, e.apply_symm_apply]

/-- A genuine bridge from a K-projective complex to the full unbounded derived
adjunction. An endomorphism inverted by degreewise left adjunction is also
inverted by the actual derived left adjoint. Its targets range over all unbounded
derived objects; no derived comparison for the free simplex is assumed. -/
theorem derivedAdjunction_map_isIso
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (adj : F ⊣ G) {L : DerivedCategory C ⥤ DerivedCategory D}
    (derivedAdj : L ⊣ G.mapDerivedCategory)
    (K : CochainComplex C ℤ) [K.IsKProjective] (f : K ⟶ K)
    [IsIso ((F.mapHomotopyCategory (.up ℤ)).map
      ((HomotopyCategory.quotient C (.up ℤ)).map f))] :
    IsIso (L.map (DerivedCategory.Q.map f)) := by
  apply isIso_of_coyoneda_map_bijective
  intro Y
  let M := DerivedCategory.Qh.objPreimage Y
  let q := HomotopyCategory.quotient C (.up ℤ)
  let ah := CWSolid.mapHomotopyCategoryAdjunction adj
  let eK := (DerivedCategory.quotientCompQhIso C).app K
  let eY := DerivedCategory.Qh.objObjPreimageIso Y
  let eGM := (G.mapDerivedCategoryFactorsh.app M).symm ≪≫ G.mapDerivedCategory.mapIso eY
  let e : ((F.mapHomotopyCategory (.up ℤ)).obj (q.obj K) ⟶ M) ≃
      (DerivedCategory.Q.obj K ⟶ G.mapDerivedCategory.obj Y) :=
    (ah.homEquiv (q.obj K) M).trans
      ((Equiv.ofBijective DerivedCategory.Qh.map
        (CochainComplex.IsKProjective.Qh_map_bijective K
          ((G.mapHomotopyCategory (.up ℤ)).obj M))).trans (Iso.homCongr eK eGM))
  have he : ∀ x, e ((F.mapHomotopyCategory (.up ℤ)).map (q.map f) ≫ x) =
      DerivedCategory.Q.map f ≫ e x := by
    intro x
    change eK.inv ≫ DerivedCategory.Qh.map
        (ah.homEquiv (q.obj K) M ((F.mapHomotopyCategory (.up ℤ)).map (q.map f) ≫ x)) ≫
        eGM.hom = DerivedCategory.Q.map f ≫
          (eK.inv ≫ DerivedCategory.Qh.map (ah.homEquiv (q.obj K) M x) ≫ eGM.hom)
    rw [ah.homEquiv_naturality_left, Functor.map_comp]
    have hn : DerivedCategory.Q.map f ≫ eK.inv =
        eK.inv ≫ DerivedCategory.Qh.map (q.map f) :=
      (DerivedCategory.quotientCompQhIso C).inv.naturality f
    simp only [← Category.assoc, hn]
  have h : Function.Bijective (fun x : DerivedCategory.Q.obj K ⟶ G.mapDerivedCategory.obj Y =>
      DerivedCategory.Q.map f ≫ x) :=
    bijective_conjugate e _ _ he
      ((isIso_iff_coyoneda_map_bijective _).1 inferInstance M)
  exact bijective_conjugate (derivedAdj.homEquiv (DerivedCategory.Q.obj K) Y).symm
    _ _ (fun x => derivedAdj.homEquiv_naturality_left_symm
      (DerivedCategory.Q.map f) x) h

end CWComparison

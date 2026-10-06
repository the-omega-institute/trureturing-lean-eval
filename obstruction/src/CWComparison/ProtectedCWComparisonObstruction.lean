/-
Copyright (c) 2026. Released under Apache 2.0.
Scope test against the literal protected all-CW natural comparison, without
changing its CW predicate, free functor, derived inclusion or singular chains.
The actual convergent-sequence endomorphism is used, not the mere absence of
closed singletons. Uses the preserved Mathlib/LeanCondensed inputs, Apache-2.0.
-/
import CWComparison.CWThickeningDerived
import CWComparison.SequenceSingularObstruction

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits LightCondensed LightCondensed.Solid LightProfinite

namespace CWComparison

/-- The free topological sequence endomorphism is obtained from the exact
protected free light-profinite presentation by the library's actual natural
topological comparison. -/
theorem derivedFreeTopSequenceDifference_isIso
    {L : DLightCondAb ⥤ DSolid} (adj : L ⊣ derivedInclusion) :
    IsIso (𝟙 _ -
      (freeLightCondAbOfTopFunctor ⋙ DerivedCategory.singleFunctor LightCondAb 0 ⋙
        L ⋙ derivedInclusion).map sequenceTopShift +
      (freeLightCondAbOfTopFunctor ⋙ DerivedCategory.singleFunctor LightCondAb 0 ⋙
        L ⋙ derivedInclusion).map sequenceTopInfinity) := by
  haveI : L.Additive := adj.left_adjoint_additive
  let D := DerivedCategory.singleFunctor LightCondAb 0 ⋙ L ⋙ derivedInclusion
  let E := Functor.isoWhiskerRight lightProfiniteToLightCondSetIsoTopCatToLightCondSet (free ℤ)
  let e := E.app ℕ∪{∞}
  let a := 𝟙 _ - freeLightCondAbOfTopFunctor.map sequenceTopShift +
    freeLightCondAbOfTopFunctor.map sequenceTopInfinity
  have hn : e.hom ≫ a = freeSequenceDifference ≫ e.hom := by
    change E.hom.app ℕ∪{∞} ≫ a = freeSequenceDifference ≫ E.hom.app ℕ∪{∞}
    simp only [a, freeSequenceDifference, Preadditive.comp_add,
      Preadditive.comp_sub, Preadditive.add_comp, Preadditive.sub_comp,
      Category.comp_id, Category.id_comp]
    have h₁ := (E.hom.naturality LightProfinite.shift).symm
    have h₂ := (E.hom.naturality sequenceInfinity).symm
    change _ ≫ freeLightCondAbOfTopFunctor.map sequenceTopShift =
      (lightProfiniteToLightCondSet ⋙ free ℤ).map LightProfinite.shift ≫ _ at h₁
    change _ ≫ freeLightCondAbOfTopFunctor.map sequenceTopInfinity =
      (lightProfiniteToLightCondSet ⋙ free ℤ).map sequenceInfinity ≫ _ at h₂
    rw [h₁, h₂]
    have hi : E.hom.app ℕ∪{∞} ≫ 𝟙 (freeLightCondAbOfTopFunctor.obj sequenceTop) =
        E.hom.app ℕ∪{∞} := Category.comp_id _
    have hi' : 𝟙 ((lightProfiniteToLightCondSet ⋙ free ℤ).obj ℕ∪{∞}) ≫
        E.hom.app ℕ∪{∞} = E.hom.app ℕ∪{∞} := Category.id_comp _
    rw [hi, hi']
  have he : a = e.inv ≫ freeSequenceDifference ≫ e.hom := by
    rw [← hn, Iso.inv_hom_id_assoc]
  haveI : IsIso (D.map freeSequenceDifference) := by
    haveI := derivedFreeSequenceDifference_isIso adj 0
    exact inferInstanceAs
      (IsIso (derivedInclusion.map (L.map
        ((DerivedCategory.singleFunctor LightCondAb 0).map freeSequenceDifference))))
  haveI : IsIso (D.map a) := by
    rw [he, D.map_comp, D.map_comp]
    infer_instance
  change IsIso (𝟙 (D.obj (freeLightCondAbOfTopFunctor.obj sequenceTop)) -
    D.map (freeLightCondAbOfTopFunctor.map sequenceTopShift) +
      D.map (freeLightCondAbOfTopFunctor.map sequenceTopInfinity))
  have hid := D.map_id (freeLightCondAbOfTopFunctor.obj sequenceTop)
  simpa only [a, Functor.map_add, Functor.map_sub, hid] using
    (inferInstance : IsIso (D.map a))

/-- An explicit obstruction to the exact NATURAL comparison on the exact
protected CW category. Its CW witness is the functorial indiscrete thickening
of the actual convergent sequence; the two continuous endomorphisms are
successor and constant infinity. This is a refutation test, not a replacement
target or a comparison supplier. -/
theorem protectedCWComparison_not_nonempty
    {L : DLightCondAb ⥤ DSolid} (adj : L ⊣ derivedInclusion) :
    ¬ Nonempty
      (CWTopCat.toTopCat ⋙ freeLightCondAbOfTopFunctor ⋙
        DerivedCategory.singleFunctor LightCondAb 0 ⋙ L ⋙ derivedInclusion ≅
          singularChainsLightCondAbCWDerivedFunctor) := by
  rintro ⟨hCW⟩
  let F := freeLightCondAbOfTopFunctor ⋙ DerivedCategory.singleFunctor LightCondAb 0 ⋙
    L ⋙ derivedInclusion
  let H := singularChainsLightCondAbDerivedFunctor
  let eF : cwThickeningTopFunctor ⋙ F ≅ F :=
    Functor.isoWhiskerRight (derivedFreeThickeningNatIso adj) derivedInclusion
  let eH : cwThickeningTopFunctor ⋙ H ≅ H := by
    let a := Functor.whiskerRight cwThickeningProjection H
    haveI : IsIso a := by
      rw [NatTrans.isIso_iff_isIso_app]
      intro X
      refine ⟨⟨H.map (cwThickeningSection.app X), ?_, ?_⟩⟩
      · change H.map (cwThickeningProjection.app X) ≫
          H.map (cwThickeningSection.app X) = 𝟙 _
        rw [← H.map_comp]
        exact (singularChainsDerived_map_eq_of_homotopy
          (cwThickeningHomotopy X)).trans (H.map_id _)
      · change H.map (cwThickeningSection.app X) ≫
          H.map (cwThickeningProjection.app X) = 𝟙 _
        rw [← H.map_comp]
        change H.map (𝟙 X) = 𝟙 _
        exact H.map_id X
    exact asIso a ≪≫ Functor.leftUnitor H
  let h : F ≅ H := eF.symm ≪≫ Functor.isoWhiskerLeft cwThickeningCWFunctor hCW ≪≫ eH
  have hn : (h.app sequenceTop).hom ≫ sequenceSingularDerivedDifference =
      (𝟙 _ - F.map sequenceTopShift + F.map sequenceTopInfinity) ≫
        (h.app sequenceTop).hom := by
    change h.hom.app sequenceTop ≫
      (𝟙 _ - H.map sequenceTopShift + H.map sequenceTopInfinity) =
        (𝟙 _ - F.map sequenceTopShift + F.map sequenceTopInfinity) ≫ h.hom.app sequenceTop
    simp only [Preadditive.comp_add,
      Preadditive.comp_sub, Preadditive.add_comp, Preadditive.sub_comp,
      Category.comp_id, Category.id_comp]
    rw [← h.hom.naturality sequenceTopShift, ← h.hom.naturality sequenceTopInfinity]
    rw [Category.comp_id (h.hom.app sequenceTop)]
  haveI : IsIso (𝟙 _ - F.map sequenceTopShift + F.map sequenceTopInfinity) :=
    derivedFreeTopSequenceDifference_isIso adj
  haveI : IsIso sequenceSingularDerivedDifference := by
    haveI : IsIso ((h.app sequenceTop).hom ≫ sequenceSingularDerivedDifference) := by
      rw [hn]
      infer_instance
    exact IsIso.of_isIso_comp_left (h.app sequenceTop).hom _
  exact sequenceSingularDerivedDifference_not_isIso inferInstance

/-- The obstruction specializes to Mathlib's genuine total-left-derived
construction, retaining ONLY its separately owned existence and adjunction. -/
theorem totalDerived_protectedCWComparison_not_nonempty
    [solidificationComplexQ.HasLeftDerivedFunctor
      (HomologicalComplex.quasiIso LightCondAb (.up ℤ))]
    (adj : totalDerivedSolidification ⊣ derivedInclusion) :
    ¬ Nonempty
      (CWTopCat.toTopCat ⋙ freeLightCondAbOfTopFunctor ⋙
        DerivedCategory.singleFunctor LightCondAb 0 ⋙ totalDerivedSolidification ⋙
          derivedInclusion ≅ singularChainsLightCondAbCWDerivedFunctor) :=
  protectedCWComparison_not_nonempty adj

end CWComparison

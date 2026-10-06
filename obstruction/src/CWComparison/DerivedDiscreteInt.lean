/-
Copyright (c) 2026. Released under Apache 2.0.
Computation of the genuine derived reflector on discrete integers, using the
preserved projectivity and full unbounded morphism calculation.
-/
import CWComparison.FreeAugmentation
import CWComparison.SingularDerived

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits LightCondensed LightCondensed.Solid

namespace CWComparison

/-- The actual discrete integers in the protected solid subcategory. -/
def solidInt : LightCondensed.Solid := ⟨_, isSolid_int⟩

/-- Discrete integral projectivity, already proved in the ambient category,
passes through the exact fully faithful protected inclusion. -/
instance solidInt_projective : Projective solidInt :=
  isSolid.ι.projective_of_map_projective
    (discrete_projective (ModuleCat.of ℤ ℤ))

/-- The derived inclusion of the integral single complex is the exact ambient
discrete integral single complex, with the protected degree convention. -/
def derivedInclusionSingleIntIso :
    derivedInclusion.obj ((DerivedCategory.singleFunctor LightCondensed.Solid 0).obj solidInt) ≅
      (DerivedCategory.singleFunctor LightCondAb 0).obj
        ((LightCondensed.discrete (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)) :=
  (isSolid.ι.mapDerivedCategoryFactors.app
    ((HomologicalComplex.single LightCondensed.Solid (.up ℤ) 0).obj solidInt)) ≪≫
      DerivedCategory.Q.mapIso
        ((HomologicalComplex.singleMapHomologicalComplex isSolid.ι (.up ℤ) 0).app solidInt)

/-- The counit is an isomorphism on the genuine solid integral object.
This does not require full faithfulness on arbitrary derived objects. -/
theorem solidIntDerived_counit_isIso
    {L : DLightCondAb ⥤ DSolid} (adj : L ⊣ derivedInclusion) :
    IsIso (adj.counit.app
      ((DerivedCategory.singleFunctor LightCondensed.Solid 0).obj solidInt)) := by
  let K : CochainComplex LightCondensed.Solid ℤ :=
    (HomologicalComplex.single LightCondensed.Solid (.up ℤ) 0).obj solidInt
  haveI : Projective solidInt.obj := discrete_projective (ModuleCat.of ℤ ℤ)
  haveI : CochainComplex.IsKProjective K := CochainComplex.isKProjective_of_projective K 0
  haveI : CochainComplex.IsKProjective
      ((HomologicalComplex.single LightCondAb (.up ℤ) 0).obj solidInt.obj) :=
    CochainComplex.isKProjective_of_projective _ 0
  haveI : CochainComplex.IsKProjective
      ((isSolid.ι.mapHomologicalComplex (.up ℤ)).obj K) := by
    apply (CochainComplex.isKProjective_iff_of_iso
      ((HomologicalComplex.singleMapHomologicalComplex isSolid.ι (.up ℤ) 0).app solidInt)).2
    change CochainComplex.IsKProjective
      ((HomologicalComplex.single LightCondAb (.up ℤ) 0).obj solidInt.obj)
    infer_instance
  exact counit_isIso_of_map_bijective adj _
    (exactDerived_map_bijective_of_isKProjective isSolid.ι K)

/-- The actual derived solidification of discrete integers is solid integers
concentrated in degree zero. This is a computation, not an assumed target iso. -/
def derivedDiscreteIntIso
    {L : DLightCondAb ⥤ DSolid} (adj : L ⊣ derivedInclusion) :
    L.obj ((DerivedCategory.singleFunctor LightCondAb 0).obj
      ((LightCondensed.discrete (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ))) ≅
        (DerivedCategory.singleFunctor LightCondensed.Solid 0).obj solidInt := by
  haveI := solidIntDerived_counit_isIso adj
  exact L.mapIso derivedInclusionSingleIntIso.symm ≪≫ asIso (adj.counit.app _)

end CWComparison

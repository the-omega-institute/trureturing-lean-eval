/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in src/licenses/LICENSE.LeanCondensed.
-/
import CWComparison.SingularProjective
import CWComparison.DerivedMap
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived

noncomputable section
open CategoryTheory Limits LightCondensed

namespace LightCondensed.Solid

/-- The exact derived inclusion is fully faithful on all morphisms from
protected singular chains. Its target is an arbitrary unbounded derived object. -/
theorem singularChainsSolidDerived_inclusion_map_bijective (X : TopCat) (Y : DSolid) :
    Function.Bijective (derivedInclusion.map :
      (singularChainsSolidDerivedFunctor.obj X ⟶ Y) → _) := by
  have : CochainComplex.IsKProjective
      ((isSolid.ι.mapHomologicalComplex (.up ℤ)).obj
        (singularChainsSolidComplexFunctor.obj X)) := singularChainsComplex_isKProjective X
  exact CWComparison.exactDerived_map_bijective_of_isKProjective isSolid.ι
    (singularChainsSolidComplexFunctor.obj X) Y

/-- Once the actual unbounded derived adjunction exists, its counit is an
isomorphism on protected singular chains. This uses proved K-projectivity on
both sides; it does not assume a comparison for free CW objects. -/
theorem singularChainsSolidDerived_counit_isIso
    {L : DLightCondAb ⥤ DSolid} (adj : L ⊣ derivedInclusion) (X : TopCat) :
    IsIso (adj.counit.app (singularChainsSolidDerivedFunctor.obj X)) :=
  CWComparison.counit_isIso_of_map_bijective adj _
    (singularChainsSolidDerived_inclusion_map_bijective X)

/-- Derived solidification fixes the protected singular chains, naturally in
every topological space, whenever the actual derived adjunction is supplied.
The source is the singular-chain complex, not the free object on the space. -/
def singularChainsDerivedReflectionNatIso
    {L : DLightCondAb ⥤ DSolid} (adj : L ⊣ derivedInclusion) :
    singularChainsLightCondAbDerivedFunctor ⋙ L ≅ singularChainsSolidDerivedFunctor := by
  have : IsIso (Functor.whiskerLeft singularChainsSolidDerivedFunctor adj.counit) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact singularChainsSolidDerived_counit_isIso adj
  exact Functor.isoWhiskerRight singularChainsSolidDerivedFactors.symm L ≪≫
    Functor.associator _ _ _ ≪≫
    asIso (Functor.whiskerLeft singularChainsSolidDerivedFunctor adj.counit) ≪≫
    Functor.rightUnitor _

/-- The actual functor whose total left derived functor occurs in holes 4–6. -/
abbrev solidificationComplexQ : CochainComplex LightCondAb ℤ ⥤ DSolid :=
  solidification.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q

/-- This uses Mathlib's genuine total-left-derived construction. Its existence
and adjunction are kept as separate, explicit unbounded-construction inputs. -/
abbrev totalDerivedSolidification
    [solidificationComplexQ.HasLeftDerivedFunctor
      (HomologicalComplex.quasiIso LightCondAb (.up ℤ))] : DLightCondAb ⥤ DSolid :=
  solidificationComplexQ.totalLeftDerived DerivedCategory.Q
    (HomologicalComplex.quasiIso LightCondAb (.up ℤ))

/-- Natural computation of the actual total left derived functor on all
protected singular chains. No resolution-existence theorem for unbounded
complexes is inferred from the bounded-above singular complex. -/
def singularChainsTotalDerivedReflectionNatIso
    [solidificationComplexQ.HasLeftDerivedFunctor
      (HomologicalComplex.quasiIso LightCondAb (.up ℤ))]
    (adj : totalDerivedSolidification ⊣ derivedInclusion) :
    singularChainsLightCondAbDerivedFunctor ⋙ totalDerivedSolidification ≅
      singularChainsSolidDerivedFunctor :=
  singularChainsDerivedReflectionNatIso adj

end LightCondensed.Solid

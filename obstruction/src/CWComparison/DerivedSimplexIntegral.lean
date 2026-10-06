/-
Copyright (c) 2026. Released under Apache 2.0.
The proved natural free-simplex augmentation with its actual integral target.
-/
import CWComparison.DerivedFreeSimplex
import CWComparison.DerivedDiscreteInt

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits LightCondensed LightCondensed.Solid

namespace CWComparison

/-- All protected free standard simplices compute solid integers in degree zero,
naturally under every simplex operator. The morphism is the canonical proved
augmentation followed by the proved integral computation. -/
def derivedFreeSimplexIntegralNatIso
    {L : DLightCondAb ⥤ DSolid} (adj : L ⊣ derivedInclusion) :
    SimplexCategory.toTop ⋙ freeLightCondAbOfTopFunctor ⋙
      DerivedCategory.singleFunctor LightCondAb 0 ⋙ L ≅
    (Functor.const SimplexCategory).obj
      ((DerivedCategory.singleFunctor LightCondensed.Solid 0).obj solidInt) :=
  derivedFreeSimplexAugmentationNatIso adj ≪≫
    (Functor.const SimplexCategory).mapIso (derivedDiscreteIntIso adj)

/-- Exact total-left-derived specialization. -/
def totalDerivedFreeSimplexIntegralNatIso
    [solidificationComplexQ.HasLeftDerivedFunctor
      (HomologicalComplex.quasiIso LightCondAb (.up ℤ))]
    (adj : totalDerivedSolidification ⊣ derivedInclusion) :
    SimplexCategory.toTop ⋙ freeLightCondAbOfTopFunctor ⋙
      DerivedCategory.singleFunctor LightCondAb 0 ⋙ totalDerivedSolidification ≅
    (Functor.const SimplexCategory).obj
      ((DerivedCategory.singleFunctor LightCondensed.Solid 0).obj solidInt) :=
  derivedFreeSimplexIntegralNatIso adj

/-- Genuine all-integer homology vanishing of the reduced free simplex. -/
theorem totalDerivedFreeSimplexReduced_homology_isZero
    [solidificationComplexQ.HasLeftDerivedFunctor
      (HomologicalComplex.quasiIso LightCondAb (.up ℤ))]
    (adj : totalDerivedSolidification ⊣ derivedInclusion)
    (n : SimplexCategory) (i : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor LightCondensed.Solid i).obj
      (totalDerivedSolidification.obj
        ((DerivedCategory.singleFunctor LightCondAb 0).obj (freeSimplexReduced n)))) :=
  (DerivedCategory.homologyFunctor LightCondensed.Solid i).map_isZero
    (totalDerivedFreeSimplexReduced_isZero adj n)

end CWComparison

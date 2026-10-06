/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in src/licenses/LICENSE.LeanCondensed.
-/
import CWComparison.FreeAugmentation
import CWComparison.FreePrism
import CWComparison.SingularDerived

noncomputable section
open CategoryTheory Limits LightCondensed LightCondensed.Solid

namespace CWComparison

/-- The actual reduced free simplex, before solidification. -/
abbrev freeSimplexReduced (n : SimplexCategory) : LightCondAb :=
  kernel (freeSimplexAugmentation.app n)

/-- The free-simplex augmentation has an honest short exact kernel sequence. -/
theorem freeSimplexKernelSequence_shortExact (n : SimplexCategory) :
    (ShortComplex.kernelSequence (freeSimplexAugmentation.app n)).ShortExact := by
  have : Epi (freeSimplexAugmentation.app n) := (freeSimplexAugmentationSplit n).epi
  refine ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact _) inferInstance ?_
  change Epi (freeSimplexAugmentation.app n)
  infer_instance

/-- The augmentation splitting is algebraic, and does not assert reduced acyclicity. -/
def freeSimplexKernelSequence_splitting (n : SimplexCategory) :
    (ShortComplex.kernelSequence (freeSimplexAugmentation.app n)).Splitting :=
  .ofExactOfSection _ (ShortComplex.kernelSequence_exact _)
    (freeSimplexAugmentationSplit n).section_ (freeSimplexAugmentationSplit n).id inferInstance

/-- The free simplex decomposes as its genuine reduced kernel plus discrete integers. -/
def freeSimplexReducedBiprodIso (n : SimplexCategory) :
    freeSimplexFunctor.obj n ≅ freeSimplexReduced n ⊞
      (LightCondensed.discrete (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ) :=
  (freeSimplexKernelSequence_splitting n).isoBinaryBiproduct

/-- The free prism contraction has constant-vertex restriction at its other endpoint,
expressed using the actual augmentation and its section. -/
theorem freeSimplexContraction_one (n : SimplexCategory) :
    freePrismEndpoint (SimplexCategory.toTop.obj n) 1 ≫
      freePrismMap (f := 𝟙 (SimplexCategory.toTop.obj n))
        (g := TopCat.ofHom (X := SimplexCategory.toTop.obj n)
          (Y := SimplexCategory.toTop.obj n) (ContinuousMap.const _ _)) (simplexContraction n) =
      freeAugmentation.app (SimplexCategory.toTop.obj n) ≫
        freeAugmentationSection (SimplexCategory.toTop.obj n)
          (ULift.up (Convexity.StdSimplex.single (R := ℝ) (0 : Fin (n.len + 1)))) := by
  rw [freePrismEndpoint_one_comp]
  change freeLightCondAbOfTopFunctor.map _ =
    (freeLightCondAbOfTopFunctor.map (collapse.app _) ≫ freePointIsoInt.hom) ≫
      (freePointIsoInt.inv ≫ freeLightCondAbOfTopFunctor.map _)
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp]
  congr 1

/-- The genuine free-object augmentation after any derived functor, natural in
all spaces. Its components are only split epimorphisms at this stage. -/
def derivedFreeAugmentation (L : DLightCondAb ⥤ DSolid) :
    freeLightCondAbOfTopFunctor ⋙ DerivedCategory.singleFunctor LightCondAb 0 ⋙ L ⟶
      (Functor.const TopCat).obj
        (L.obj ((DerivedCategory.singleFunctor LightCondAb 0).obj
          ((LightCondensed.discrete (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)))) where
  app X := L.map ((DerivedCategory.singleFunctor LightCondAb 0).map (freeAugmentation.app X))
  naturality X Y f := by
    change L.map ((DerivedCategory.singleFunctor LightCondAb 0).map
        (freeLightCondAbOfTopFunctor.map f)) ≫
      L.map ((DerivedCategory.singleFunctor LightCondAb 0).map (freeAugmentation.app Y)) =
        L.map ((DerivedCategory.singleFunctor LightCondAb 0).map (freeAugmentation.app X)) ≫ 𝟙 _
    rw [Category.comp_id, ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    have h := freeAugmentation.naturality f
    simp only [Functor.const_obj_map] at h
    rw [h]
    congr 2

/-- The actual total-left-derived specialization uses precisely the separately
owned unbounded construction premise; it assumes no free-simplex comparison. -/
abbrev totalDerivedFreeAugmentation
    [solidificationComplexQ.HasLeftDerivedFunctor
      (HomologicalComplex.quasiIso LightCondAb (.up ℤ))] :=
  derivedFreeAugmentation totalDerivedSolidification

/-- The free-simplex augmentation stays split after the actual derived construction. -/
def totalDerivedFreeSimplexAugmentationSplit
    [solidificationComplexQ.HasLeftDerivedFunctor
      (HomologicalComplex.quasiIso LightCondAb (.up ℤ))] (n : SimplexCategory) :
    SplitEpi (totalDerivedFreeAugmentation.app (SimplexCategory.toTop.obj n)) :=
  (freeSimplexAugmentationSplit n).map
    (DerivedCategory.singleFunctor LightCondAb 0 ⋙ totalDerivedSolidification)

end CWComparison

/-
Copyright (c) 2026. Released under Apache 2.0.
Natural augmentation equivalence and actual reduced derived acyclicity of every
protected free topological standard simplex. No simplex comparison is a premise.
-/
import CWComparison.DerivedFreeHomotopy
import CWComparison.FreeSimplex

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits LightCondensed LightCondensed.Solid

namespace CWComparison

/-- The canonical free-simplex augmentation is an equivalence after the genuine
unbounded derived left adjoint, in every simplex dimension. -/
theorem derivedFreeSimplexAugmentation_isIso
    {L : DLightCondAb ⥤ DSolid} (adj : L ⊣ derivedInclusion) (n : SimplexCategory) :
    IsIso ((derivedFreeAugmentation L).app (SimplexCategory.toTop.obj n)) := by
  let D := DerivedCategory.singleFunctor LightCondAb 0 ⋙ L
  let X := SimplexCategory.toTop.obj n
  let x : X := ULift.up (Convexity.StdSimplex.single (R := ℝ) (0 : Fin (n.len + 1)))
  let c : X ⟶ X := TopCat.ofHom (ContinuousMap.const _ x)
  have hc : freeLightCondAbOfTopFunctor.map c =
      freeAugmentation.app X ≫ freeAugmentationSection X x := by
    change freeLightCondAbOfTopFunctor.map c =
      (freeLightCondAbOfTopFunctor.map (collapse.app X) ≫ freePointIsoInt.hom) ≫
        (freePointIsoInt.inv ≫ freeLightCondAbOfTopFunctor.map (collapseSplit X x).section_)
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Functor.map_comp]
    congr 1
  have h := derivedFreeMap_homotopy adj (simplexContraction n)
  change D.map (freeLightCondAbOfTopFunctor.map (𝟙 X)) =
    D.map (freeLightCondAbOfTopFunctor.map c) at h
  have hs : D.map (freeAugmentation.app X) ≫
      D.map (freeAugmentationSection X x) = 𝟙 _ := by
    rw [← Functor.map_comp, ← hc, ← h, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_id]
  change IsIso (D.map (freeAugmentation.app X))
  exact ⟨⟨D.map (freeAugmentationSection X x), hs, by
    rw [← Functor.map_comp, freeAugmentationSection_comp]
    exact D.map_id _⟩⟩

/-- The inverses arise from invertibility of the already natural augmentation.
Thus all simplex operators commute; chosen vertices need not be natural. -/
def derivedFreeSimplexAugmentationNatIso
    {L : DLightCondAb ⥤ DSolid} (adj : L ⊣ derivedInclusion) :
    SimplexCategory.toTop ⋙ freeLightCondAbOfTopFunctor ⋙
      DerivedCategory.singleFunctor LightCondAb 0 ⋙ L ≅
    (Functor.const SimplexCategory).obj
      (L.obj ((DerivedCategory.singleFunctor LightCondAb 0).obj
        ((LightCondensed.discrete (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)))) := by
  let a := Functor.whiskerLeft SimplexCategory.toTop (derivedFreeAugmentation L)
  haveI : IsIso a := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact derivedFreeSimplexAugmentation_isIso adj
  exact asIso a

/-- Actual vanishing in the full unbounded solid derived category of the
protected reduced free simplex. This is stronger than reflected exactness. -/
theorem derivedFreeSimplexReduced_isZero
    {L : DLightCondAb ⥤ DSolid} (adj : L ⊣ derivedInclusion) (n : SimplexCategory) :
    IsZero (L.obj ((DerivedCategory.singleFunctor LightCondAb 0).obj
      (freeSimplexReduced n))) := by
  letI : L.Additive := adj.left_adjoint_additive
  let D := DerivedCategory.singleFunctor LightCondAb 0 ⋙ L
  let a := freeSimplexAugmentation.app n
  let s := freeSimplexKernelSequence_splitting n
  haveI : IsIso (D.map a) := derivedFreeSimplexAugmentation_isIso adj n
  have hf : D.map (kernel.ι a) = 0 := by
    apply (cancel_mono (D.map a)).1
    rw [← Functor.map_comp, kernel.condition, D.map_zero, zero_comp]
  apply (IsZero.iff_id_eq_zero _).2
  change 𝟙 (D.obj (kernel a)) = 0
  have hr : kernel.ι a ≫ s.r = 𝟙 (kernel a) := s.f_r
  rw [← D.map_id, ← hr]
  change D.map (kernel.ι a ≫ s.r) = 0
  rw [Functor.map_comp, hf, zero_comp]

/-- Exact total-left-derived specialization, retaining its genuine construction
and adjunction as the only separately owned premises. -/
def totalDerivedFreeSimplexAugmentationNatIso
    [solidificationComplexQ.HasLeftDerivedFunctor
      (HomologicalComplex.quasiIso LightCondAb (.up ℤ))]
    (adj : totalDerivedSolidification ⊣ derivedInclusion) :=
  derivedFreeSimplexAugmentationNatIso adj

theorem totalDerivedFreeSimplexReduced_isZero
    [solidificationComplexQ.HasLeftDerivedFunctor
      (HomologicalComplex.quasiIso LightCondAb (.up ℤ))]
    (adj : totalDerivedSolidification ⊣ derivedInclusion) (n : SimplexCategory) :
    IsZero (totalDerivedSolidification.obj
      ((DerivedCategory.singleFunctor LightCondAb 0).obj (freeSimplexReduced n))) :=
  derivedFreeSimplexReduced_isZero adj n

end CWComparison

/-
Copyright (c) 2026. Released under Apache 2.0.
Binary cancellation on actual derived free condensed objects.
Geometry attributed to Rodríguez Camargo, Notes on Solid Geometry,
arXiv:2603.03012, proof of Proposition 3.2.5.
-/
import CWComparison.DerivedTensorInversion
import CWComparison.FreeBinaryHomotopy
import Mathlib.CategoryTheory.Adjunction.Additive

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits LightCondensed LightCondensed.Solid MonoidalCategory

namespace CWComparison

private theorem binary_cancellation
    {C : Type*} [Category* C] [Preadditive C] {A E Y : C}
    (t u v : E ⟶ E) [IsIso t] (h : E ⟶ Y) (a b : A ⟶ E)
    (hut : u ≫ t = t ≫ v) (huh : u ≫ h = h)
    (hat : a ≫ t = a - b) (hav : a ≫ v = b) : a ≫ h = 0 := by
  let k := inv t ≫ h
  have htk : t ≫ k = h := by simp [k]
  have hvk : v ≫ k = k := by
    apply (cancel_epi t).1
    rw [← Category.assoc, ← hut, Category.assoc, htk, huh]
  calc
    a ≫ h = a ≫ t ≫ k := by rw [htk]
    _ = (a - b) ≫ k := by rw [← Category.assoc, hat]
    _ = 0 := by rw [Preadditive.sub_comp, ← hav, Category.assoc, hvk, sub_self]

/-- Every continuous homotopy gives equality of the actual derived free maps.
No restriction on the spaces, no presumed homotopy invariance and no presumed
simplex comparison is used. -/
theorem derivedFreeMap_homotopy
    {L : DLightCondAb ⥤ DSolid} (adj : L ⊣ derivedInclusion)
    {X Y : TopCat} {f g : X ⟶ Y} (H : ContinuousMap.Homotopy f.hom g.hom) :
    L.map ((DerivedCategory.singleFunctor LightCondAb 0).map
      (freeLightCondAbOfTopFunctor.map f)) =
    L.map ((DerivedCategory.singleFunctor LightCondAb 0).map
      (freeLightCondAbOfTopFunctor.map g)) := by
  letI : L.Additive := adj.left_adjoint_additive
  let D := DerivedCategory.singleFunctor LightCondAb 0 ⋙ L
  let B := freeLightCondAbOfTopFunctor.obj X
  let t := D.map (oneMinusShift ▷ B)
  let u := D.map ((PbinaryLeft + PbinaryRight) ▷ B)
  let v := D.map (PbinaryLeft ▷ B)
  let h := D.map (freeBinaryHomotopy H)
  let a := D.map (Pfinite 0 ▷ B)
  let b := D.map (Pfinite 1 ▷ B)
  haveI : IsIso t := derivedAdjunction_tensor_oneMinusShift_isIso adj B 0
  have hut : u ≫ t = t ≫ v := by
    dsimp [u, t, v]
    rw [← Functor.map_comp, ← Functor.map_comp, ← comp_whiskerRight,
      ← comp_whiskerRight, binary_P_subdivision]
  have huh : u ≫ h = h := by
    change D.map ((PbinaryLeft + PbinaryRight) ▷ freeLightCondAbOfTopFunctor.obj X) ≫
      D.map (freeBinaryHomotopy H) = D.map (freeBinaryHomotopy H)
    rw [← Functor.map_comp]
    exact congrArg D.map (freeBinaryHomotopy_subdivision H)
  have hat : a ≫ t = a - b := by
    dsimp [a, t, b]
    rw [← Functor.map_comp, ← comp_whiskerRight, Pfinite_oneMinusShift]
    change D.map ((tensorRight B).map (Pfinite 0 - Pfinite 1)) = _
    rw [(tensorRight B).map_sub, D.map_sub]
    rfl
  have hav : a ≫ v = b := by
    dsimp [a, v, b]
    rw [← Functor.map_comp, ← comp_whiskerRight, Pfinite_binaryLeft]
  have hzero := binary_cancellation t u v h a b hut huh hat hav
  have hroot : D.map (freeBinaryRootIso X).hom ≫
      D.map (freeLightCondAbOfTopFunctor.map g - freeLightCondAbOfTopFunctor.map f) = 0 := by
    rw [← Functor.map_comp, ← freeBinaryHomotopy_root, Functor.map_comp]
    exact hzero
  have hz : D.map (freeLightCondAbOfTopFunctor.map g -
      freeLightCondAbOfTopFunctor.map f) = 0 := by
    apply (cancel_epi (D.map (freeBinaryRootIso X).hom)).1
    rw [hroot, comp_zero]
  rw [D.map_sub] at hz
  exact (sub_eq_zero.mp hz).symm

/-- The same equality for the actual total left derived functor. -/
theorem totalDerivedFreeMap_homotopy
    [solidificationComplexQ.HasLeftDerivedFunctor
      (HomologicalComplex.quasiIso LightCondAb (.up ℤ))]
    (adj : totalDerivedSolidification ⊣ derivedInclusion)
    {X Y : TopCat} {f g : X ⟶ Y} (H : ContinuousMap.Homotopy f.hom g.hom) :
    totalDerivedSolidification.map ((DerivedCategory.singleFunctor LightCondAb 0).map
      (freeLightCondAbOfTopFunctor.map f)) =
    totalDerivedSolidification.map ((DerivedCategory.singleFunctor LightCondAb 0).map
      (freeLightCondAbOfTopFunctor.map g)) :=
  derivedFreeMap_homotopy adj H

end CWComparison

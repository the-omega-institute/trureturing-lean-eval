/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in src/licenses/LICENSE.LeanCondensed.

A genuine morphism of free condensed objects from every continuous homotopy.
No homotopy invariance or derived simplex computation is assumed.
-/
import CWComparison.BinaryEdgeDescent
import CWComparison.FreePrism
import Mathlib.Topology.Category.TopCat.Monoidal

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits LightCondensed LightCondensed.Solid MonoidalCategory
open LightProfinite OnePoint

namespace CWComparison

local instance : topCatToLightCondSet.IsRightAdjoint := LightCondSet.topCatAdjunction.isRightAdjoint
local instance : topCatToLightCondSet.Monoidal :=
  (Functor.Monoidal.nonempty_monoidal_iff_preservesFiniteProducts _).mpr inferInstance |>.some

/-- Tensor products of the genuine protected free topological objects. -/
def freeTopTensorIso (X Y : TopCat) :
    freeLightCondAbOfTopFunctor.obj X ⊗ freeLightCondAbOfTopFunctor.obj Y ≅
      freeLightCondAbOfTopFunctor.obj (X ⊗ Y) :=
  Functor.Monoidal.μIso freeLightCondAbOfTopFunctor X Y

/-- The root parameter, removed by an actual isomorphism. -/
def freeBinaryRootIso (X : TopCat) :
    (free ℤ).obj (LightProfinite.of PUnit).toCondensed ⊗
      freeLightCondAbOfTopFunctor.obj X ≅ freeLightCondAbOfTopFunctor.obj X :=
  (freeProfiniteTopNatIso.app (LightProfinite.of PUnit) ⊗ᵢ Iso.refl _) ≪≫
    freeTopTensorIso (𝟙_ TopCat) X ≪≫ freeLightCondAbOfTopFunctor.mapIso (λ_ X)

/-- The shrinking free edge sequence tensored with all continuous X-families,
then evaluated in the homotopy prism. This is an actual condensed morphism. -/
def freeBinaryHomotopy {X Y : TopCat} {f g : X ⟶ Y}
    (H : ContinuousMap.Homotopy f.hom g.hom) :
    P ⊗ freeLightCondAbOfTopFunctor.obj X ⟶ freeLightCondAbOfTopFunctor.obj Y :=
  (binaryEdgePMap ▷ freeLightCondAbOfTopFunctor.obj X) ≫
    (freeTopTensorIso (TopCat.of unitInterval) X).hom ≫
      freeLightCondAbOfTopFunctor.map (TopCat.ofHom H.toContinuousMap)

/-- The binary subdivision relation holds simultaneously for every parameter X. -/
theorem freeBinaryHomotopy_subdivision {X Y : TopCat} {f g : X ⟶ Y}
    (H : ContinuousMap.Homotopy f.hom g.hom) :
    ((PbinaryLeft + PbinaryRight) ▷ freeLightCondAbOfTopFunctor.obj X) ≫
      freeBinaryHomotopy H = freeBinaryHomotopy H := by
  dsimp [freeBinaryHomotopy]
  rw [← comp_whiskerRight_assoc, binaryEdgePMap_subdivision]

/-- The root of the genuine condensed homotopy is the exact endpoint difference.
The prefactor is an isomorphism, not evaluation at ordinary points. -/
theorem freeBinaryHomotopy_root {X Y : TopCat} {f g : X ⟶ Y}
    (H : ContinuousMap.Homotopy f.hom g.hom) :
    (Pfinite 0 ▷ freeLightCondAbOfTopFunctor.obj X) ≫ freeBinaryHomotopy H =
      (freeBinaryRootIso X).hom ≫
        (freeLightCondAbOfTopFunctor.map g - freeLightCondAbOfTopFunctor.map f) := by
  let i (t : unitInterval) : (𝟙_ TopCat) ⟶ TopCat.of unitInterval :=
    TopCat.ofHom (ContinuousMap.const _ t)
  have h (t : unitInterval) :
      (freeLightCondAbOfTopFunctor.map (i t) ▷ freeLightCondAbOfTopFunctor.obj X) ≫
        (freeTopTensorIso (TopCat.of unitInterval) X).hom =
      (freeTopTensorIso (𝟙_ TopCat) X).hom ≫ freeLightCondAbOfTopFunctor.map (i t ▷ X) :=
    Functor.LaxMonoidal.μ_natural_left freeLightCondAbOfTopFunctor (i t) X
  have h₁ : (i 1 ▷ X) ≫ TopCat.ofHom H.toContinuousMap = (λ_ X).hom ≫ g := by
    ext p
    exact H.map_one_left p.2
  have h₀ : (i 0 ▷ X) ≫ TopCat.ofHom H.toContinuousMap = (λ_ X).hom ≫ f := by
    ext p
    exact H.map_zero_left p.2
  have h' (t : unitInterval) :
      (freeLightCondAbOfTopFunctor.map (i t) ▷ freeLightCondAbOfTopFunctor.obj X) ≫
        (freeTopTensorIso (TopCat.of unitInterval) X).hom ≫
          freeLightCondAbOfTopFunctor.map (TopCat.ofHom H.toContinuousMap) =
      (freeTopTensorIso (𝟙_ TopCat) X).hom ≫
        freeLightCondAbOfTopFunctor.map (i t ▷ X) ≫
          freeLightCondAbOfTopFunctor.map (TopCat.ofHom H.toContinuousMap) := by
    simpa only [Category.assoc] using congrArg
      (fun k => k ≫ freeLightCondAbOfTopFunctor.map (TopCat.ofHom H.toContinuousMap)) (h t)
  dsimp [freeBinaryHomotopy]
  rw [← comp_whiskerRight_assoc, binaryEdgePMap_root, comp_whiskerRight]
  have hsub : (freeLightCondAbOfTopFunctor.map (i 1) - freeLightCondAbOfTopFunctor.map (i 0)) ▷
      freeLightCondAbOfTopFunctor.obj X =
    (freeLightCondAbOfTopFunctor.map (i 1) ▷ freeLightCondAbOfTopFunctor.obj X) -
      (freeLightCondAbOfTopFunctor.map (i 0) ▷ freeLightCondAbOfTopFunctor.obj X) :=
    (tensorRight (freeLightCondAbOfTopFunctor.obj X)).map_sub
  simp only [Category.assoc]
  change _ ≫ ((freeLightCondAbOfTopFunctor.map (i 1) -
    freeLightCondAbOfTopFunctor.map (i 0)) ▷ freeLightCondAbOfTopFunctor.obj X) ≫ _ = _
  rw [hsub]
  simp only [Preadditive.sub_comp, Preadditive.comp_sub, Category.assoc]
  change _ ≫ ((freeLightCondAbOfTopFunctor.map (i 1) ▷ _) ≫ _) -
    _ ≫ ((freeLightCondAbOfTopFunctor.map (i 0) ▷ _) ≫ _) = _
  erw [h' 1, h' 0]
  simp only [Category.assoc, ← Functor.map_comp]
  erw [h₁, h₀]
  simp only [Functor.map_comp, ← Preadditive.comp_sub]
  simp [freeBinaryRootIso, Category.assoc]

end CWComparison

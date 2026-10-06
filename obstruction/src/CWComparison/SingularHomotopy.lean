/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in src/licenses/LICENSE.LeanCondensed.

The topological prism homotopy is Mathlib's result of Joël Riou and Fabian
Odermatt, built on the earlier singular-homology work of Brendan Seamus Murphy.
This file transports it to the exact protected complexes and their solid lift.
-/
import CWSolid.SingularSolid
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance

noncomputable section
open CategoryTheory Limits LightCondensed

namespace LightCondensed.Solid

/-- The prism homotopy on the exact protected singular complexes, with the
protected degree convention. No CW or finiteness hypothesis is used. -/
def singularChainsComplexHomotopy {X Y : TopCat} {f g : X ⟶ Y}
    (H : TopCat.Homotopy f g) :
    Homotopy (singularChainsLightCondAbComplexFunctor.map f)
      (singularChainsLightCondAbComplexFunctor.map g) := by
  let F := LightCondensed.discrete (ModuleCat ℤ)
  have : F.Additive := Functor.additive_of_preserves_binary_products F
  exact (F.mapHomotopy (H.singularChainComplexFunctorObjMap
    (ModuleCat.of ℤ ℤ))).extend ComplexShape.embeddingDownNat

/-- The prism homotopy lifts into the genuine solid category using the full
faithfulness of the exact inclusion, rather than a redefined chain functor. -/
def singularChainsSolidComplexHomotopy {X Y : TopCat} {f g : X ⟶ Y}
    (H : TopCat.Homotopy f g) :
    Homotopy (singularChainsSolidComplexFunctor.map f)
      (singularChainsSolidComplexFunctor.map g) :=
  isSolid.ι.preimageHomotopy (singularChainsComplexHomotopy H)

theorem singularChainsDerived_map_eq_of_homotopy
    {X Y : TopCat} {f g : X ⟶ Y} (H : TopCat.Homotopy f g) :
    singularChainsLightCondAbDerivedFunctor.map f =
      singularChainsLightCondAbDerivedFunctor.map g :=
  DerivedCategory.Q_map_eq_of_homotopy _ (singularChainsComplexHomotopy H)

theorem singularChainsSolidDerived_map_eq_of_homotopy
    {X Y : TopCat} {f g : X ⟶ Y} (H : TopCat.Homotopy f g) :
    singularChainsSolidDerivedFunctor.map f = singularChainsSolidDerivedFunctor.map g :=
  DerivedCategory.Q_map_eq_of_homotopy _ (singularChainsSolidComplexHomotopy H)

/-- A topological homotopy equivalence induces an actual isomorphism of the
protected singular-chain objects in the solid derived category. -/
def singularChainsSolidDerivedIsoOfHomotopyInverse
    {X Y : TopCat} (f : X ⟶ Y) (g : Y ⟶ X)
    (hf : TopCat.Homotopy (f ≫ g) (𝟙 X))
    (hg : TopCat.Homotopy (g ≫ f) (𝟙 Y)) :
    singularChainsSolidDerivedFunctor.obj X ≅ singularChainsSolidDerivedFunctor.obj Y where
  hom := singularChainsSolidDerivedFunctor.map f
  inv := singularChainsSolidDerivedFunctor.map g
  hom_inv_id := by
    rw [← Functor.map_comp, singularChainsSolidDerived_map_eq_of_homotopy hf,
      CategoryTheory.Functor.map_id]
  inv_hom_id := by
    rw [← Functor.map_comp, singularChainsSolidDerived_map_eq_of_homotopy hg,
      CategoryTheory.Functor.map_id]

end LightCondensed.Solid

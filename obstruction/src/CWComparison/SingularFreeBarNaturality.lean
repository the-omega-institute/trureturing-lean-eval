/-
Copyright (c) 2026. Released under Apache 2.0.
Functoriality in every topological space of the actual free singular bar
and its chain-level evaluation, before choosing any CW decomposition.
-/
import CWComparison.SingularFreeBarAugmentation

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits Opposite LightCondensed LightCondensed.Solid AlgebraicTopology
open scoped Simplicial

namespace CWComparison

/-- Postcomposition of every singular simplex in a bar string. -/
def singularFreeBarPostcompose {X Y : TopCat} (f : X ⟶ Y) :
    singularFreeBar X ⟶ singularFreeBar Y where
  app n := Sigma.desc (fun c : ComposableArrows (singularSimplexCategory X) n.unop.len =>
    Sigma.ι (fun d : ComposableArrows (singularSimplexCategory Y) n.unop.len =>
      (singularFreeSimplexDiagram Y).obj d.left) (c ⋙ CostructuredArrow.map f))
  naturality {m n} φ := by
    apply Sigma.hom_ext
    intro c
    simp only [singularFreeBar, singularFreeBarMap, Category.assoc,
      Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
    rfl

private theorem singularString_id (X : TopCat) (n : ℕ)
    (c : ComposableArrows (singularSimplexCategory X) n) :
    c ⋙ CostructuredArrow.map (𝟙 X) = c := by
  refine CategoryTheory.Functor.ext
    (fun i => CostructuredArrow.map_id (S := SimplexCategory.toTop) (f := c.obj i)) ?_
  intro i j u
  apply CostructuredArrow.hom_ext
  simp

private theorem singularString_comp {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : ℕ) (c : ComposableArrows (singularSimplexCategory X) n) :
    c ⋙ CostructuredArrow.map (f ≫ g) =
      (c ⋙ CostructuredArrow.map f) ⋙ CostructuredArrow.map g := by
  refine CategoryTheory.Functor.ext
    (fun i => CostructuredArrow.map_comp (S := SimplexCategory.toTop)
      (f := f) (f' := g) (h := c.obj i)) ?_
  intro i j u
  apply CostructuredArrow.hom_ext
  simp

/-- The genuine free singular bar is natural for all continuous maps. -/
def singularFreeBarFunctor : TopCat ⥤ SimplicialObject LightCondAb where
  obj := singularFreeBar
  map := singularFreeBarPostcompose
  map_id X := by
    apply NatTrans.ext
    funext n
    apply Sigma.hom_ext
    intro c
    simp only [singularFreeBarPostcompose, Sigma.ι_comp_desc, NatTrans.id_app, Category.comp_id]
    erw [Category.comp_id]
    simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using
      (Sigma.eqToHom_comp_ι
        (fun d : ComposableArrows (singularSimplexCategory X) n.unop.len =>
          (singularFreeSimplexDiagram X).obj d.left)
        (singularString_id X n.unop.len c))
  map_comp f g := by
    apply NatTrans.ext
    funext n
    apply Sigma.hom_ext
    intro c
    simp only [singularFreeBarPostcompose, NatTrans.comp_app, Category.assoc,
      Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
    simpa only [eqToHom_refl, Category.id_comp] using
      (Sigma.eqToHom_comp_ι
        (fun d : ComposableArrows (singularSimplexCategory _) n.unop.len =>
          (singularFreeSimplexDiagram _).obj d.left)
        (singularString_comp f g n.unop.len c))

/-- Evaluation is compatible with postcomposition in every bar degree. -/
theorem singularFreeBarPostcompose_augmentation {X Y : TopCat} (f : X ⟶ Y)
    (n : SimplexCategoryᵒᵖ) :
    (singularFreeBarPostcompose f).app n ≫ (singularFreeBarAugmentation Y).app n =
      (singularFreeBarAugmentation X).app n ≫ freeLightCondAbOfTopFunctor.map f := by
  apply Sigma.hom_ext
  intro c
  simp only [singularFreeBarPostcompose, singularFreeBarAugmentation,
    Category.assoc, Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
  exact freeLightCondAbOfTopFunctor.map_comp c.left.hom f

/-- The augmented construction is strictly natural before passage to chains. -/
def singularFreeBarAugmentedFunctor : TopCat ⥤ SimplicialObject.Augmented LightCondAb where
  obj := singularFreeBarAugmented
  map f := {
    left := singularFreeBarPostcompose f
    right := freeLightCondAbOfTopFunctor.map f
    w := by
      apply NatTrans.ext
      funext n
      exact singularFreeBarPostcompose_augmentation f n }
  map_id X := by
    apply SimplicialObject.Augmented.hom_ext
    · exact singularFreeBarFunctor.map_id X
    · exact freeLightCondAbOfTopFunctor.map_id X
  map_comp f g := by
    apply SimplicialObject.Augmented.hom_ext
    · exact singularFreeBarFunctor.map_comp f g
    · exact freeLightCondAbOfTopFunctor.map_comp f g

end CWComparison

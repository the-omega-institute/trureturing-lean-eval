/-
Copyright (c) 2026. Released under Apache 2.0.
The actual coefficient collapse from the canonical free singular bar to the
discrete integral chains on its indexing nerve. Total-derived equivalence and
identification with protected singular chains are further proof obligations.
-/
import CWComparison.SingularFreeBarNaturality
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits Opposite LightCondensed LightCondensed.Solid AlgebraicTopology
open scoped Simplicial

namespace CWComparison

/-- The genuine discrete integral bar on all finite strings of singular simplices. -/
abbrev singularDiscreteBar (X : TopCat) : SimplicialObject LightCondAb :=
  nerve (singularSimplexCategory X) ⋙
    (sigmaConst.obj ((LightCondensed.discrete (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)))

/-- Canonical simplex augmentation, summed over every string, in all bar degrees. -/
def singularFreeBarCollapse (X : TopCat) : singularFreeBar X ⟶ singularDiscreteBar X where
  app n := Sigma.desc (fun c : ComposableArrows (singularSimplexCategory X) n.unop.len =>
    freeAugmentation.app (SimplexCategory.toTop.obj c.left.left) ≫
      Sigma.ι (fun _ : ComposableArrows (singularSimplexCategory X) n.unop.len =>
        (LightCondensed.discrete (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)) c)
  naturality {m n} φ := by
    apply Sigma.hom_ext
    intro c
    simp only [singularFreeBar, singularFreeBarMap, Sigma.ι_comp_desc_assoc,
      Sigma.ι_comp_desc, Category.assoc]
    change freeLightCondAbOfTopFunctor.map
        (SimplexCategory.toTop.map
          (c.map (homOfLE (Fin.zero_le ((barOrdinalFunctor φ.unop).obj 0)))).left) ≫
      freeAugmentation.app _ ≫
        Sigma.ι (fun _ : ComposableArrows (singularSimplexCategory X) n.unop.len =>
          (LightCondensed.discrete (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ))
            (c.whiskerLeft (barOrdinalFunctor φ.unop)) =
        freeAugmentation.app _ ≫
          Sigma.ι (fun _ : ComposableArrows (singularSimplexCategory X) m.unop.len =>
            (LightCondensed.discrete (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)) c ≫
              (singularDiscreteBar X).map φ
    simp only [singularDiscreteBar, Functor.comp_map, sigmaConst,
      Sigma.ι_comp_map', Category.id_comp]
    have h := freeAugmentation.naturality
      (SimplexCategory.toTop.map
        (c.map (homOfLE (Fin.zero_le ((barOrdinalFunctor φ.unop).obj 0)))).left)
    simp only [Functor.const_obj_map, Category.comp_id] at h
    erw [← Category.assoc, h, Category.comp_id]
    rfl

/-- Actual postcomposition on the discrete integral nerve bar. -/
def singularDiscreteBarPostcompose {X Y : TopCat} (f : X ⟶ Y) :
    singularDiscreteBar X ⟶ singularDiscreteBar Y :=
  Functor.whiskerRight (nerveMap (CostructuredArrow.map f))
    (sigmaConst.obj ((LightCondensed.discrete (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)))

/-- The coefficient collapse commutes with every continuous map, before any
CW decomposition or derived comparison is chosen. -/
theorem singularFreeBarPostcompose_collapse {X Y : TopCat} (f : X ⟶ Y) :
    singularFreeBarPostcompose f ≫ singularFreeBarCollapse Y =
      singularFreeBarCollapse X ≫ singularDiscreteBarPostcompose f := by
  apply NatTrans.ext
  funext n
  apply Sigma.hom_ext
  intro c
  simp only [NatTrans.comp_app, singularFreeBarPostcompose, singularFreeBarCollapse,
    Category.assoc, Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
  change freeAugmentation.app _ ≫
      Sigma.ι (fun _ : ComposableArrows (singularSimplexCategory Y) n.unop.len =>
        (LightCondensed.discrete (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ))
          (c ⋙ CostructuredArrow.map f) =
    freeAugmentation.app _ ≫
      Sigma.ι (fun _ : ComposableArrows (singularSimplexCategory X) n.unop.len =>
        (LightCondensed.discrete (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)) c ≫
          (singularDiscreteBarPostcompose f).app n
  simp only [singularDiscreteBarPostcompose, Functor.whiskerRight_app,
    sigmaConst, Sigma.ι_comp_map', Category.id_comp]
  rfl

/-- An honest chain map in every degree; its derived invertibility is not a premise. -/
abbrev singularFreeBarComplexCollapse (X : TopCat) :
    singularFreeBarComplex X ⟶
      (nerve (singularSimplexCategory X)).chainComplex
        ((LightCondensed.discrete (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)) :=
  AlternatingFaceMapComplex.map (singularFreeBarCollapse X)

/-- The collapse map viewed in the actual unbounded ambient derived category. -/
abbrev singularFreeBarDerivedCollapse (X : TopCat) :
    DerivedCategory.Q.obj (singularFreeBarUnbounded X) ⟶
      DerivedCategory.Q.obj
        (((nerve (singularSimplexCategory X)).chainComplex
          ((LightCondensed.discrete (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ))).extend
            ComplexShape.embeddingDownNat) :=
  DerivedCategory.Q.map (HomologicalComplex.extendMap
    (singularFreeBarComplexCollapse X) ComplexShape.embeddingDownNat)

end CWComparison

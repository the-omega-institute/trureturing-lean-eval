/-
Copyright (c) 2026. Released under Apache 2.0.
The actual augmented free singular-simplex bar complex in all degrees.
No augmentation equivalence or CW descent is assumed.
-/
import CWComparison.SingularFreeBar
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits Opposite LightCondensed LightCondensed.Solid AlgebraicTopology
open scoped Simplicial

namespace CWComparison

/-- Actual evaluation of all strings of singular simplices in the target. -/
def singularFreeBarAugmentation (X : TopCat) :
    singularFreeBar X ⟶ (Functor.const SimplexCategoryᵒᵖ).obj
      (freeLightCondAbOfTopFunctor.obj X) where
  app n := Sigma.desc (fun c : ComposableArrows (singularSimplexCategory X) n.unop.len =>
    freeLightCondAbOfTopFunctor.map c.left.hom)
  naturality {m n} f := by
    apply Sigma.hom_ext
    intro c
    simp only [singularFreeBar, singularFreeBarMap, Category.assoc,
      Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc, Functor.const_obj_map, Category.comp_id]
    change freeLightCondAbOfTopFunctor.map
        (SimplexCategory.toTop.map
          (c.map (homOfLE (Fin.zero_le
            ((barOrdinalFunctor f.unop).obj 0)))).left) ≫
      freeLightCondAbOfTopFunctor.map _ = freeLightCondAbOfTopFunctor.map _
    rw [← Functor.map_comp]
    exact congrArg freeLightCondAbOfTopFunctor.map (CostructuredArrow.w
      (c.map (homOfLE (Fin.zero_le ((barOrdinalFunctor f.unop).obj 0)))))

/-- The full augmented simplicial free resolution candidate, before deriving.
Its being a resolution after solidification is a remaining theorem. -/
def singularFreeBarAugmented (X : TopCat) : SimplicialObject.Augmented LightCondAb where
  left := singularFreeBar X
  right := freeLightCondAbOfTopFunctor.obj X
  hom := singularFreeBarAugmentation X

/-- The actual chain complex in all natural bar degrees. -/
abbrev singularFreeBarComplex (X : TopCat) : ChainComplex LightCondAb ℕ :=
  AlternatingFaceMapComplex.obj (singularFreeBar X)

/-- Evaluation is an honest chain map, without assuming it a quasi-isomorphism. -/
abbrev singularFreeBarComplexAugmentation (X : TopCat) :
    singularFreeBarComplex X ⟶ (ChainComplex.single₀ LightCondAb).obj
      (freeLightCondAbOfTopFunctor.obj X) :=
  AlternatingFaceMapComplex.ε.app (singularFreeBarAugmented X)

/-- The actual full unbounded source underlying the future CW comparison. -/
abbrev singularFreeBarUnbounded (X : TopCat) : CochainComplex LightCondAb ℤ :=
  (singularFreeBarComplex X).extend ComplexShape.embeddingDownNat

/-- Evaluation in the exact protected degree-zero free condensed object,
not merely in a bounded derived category. -/
def singularFreeBarUnboundedAugmentation (X : TopCat) :
    singularFreeBarUnbounded X ⟶
      (HomologicalComplex.single LightCondAb (.up ℤ) 0).obj
        (freeLightCondAbOfTopFunctor.obj X) :=
  (HomologicalComplex.extendMap (singularFreeBarComplexAugmentation X)
    ComplexShape.embeddingDownNat) ≫
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat
        (freeLightCondAbOfTopFunctor.obj X) 0 0 (by simp)).hom

end CWComparison

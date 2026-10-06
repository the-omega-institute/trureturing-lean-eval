/-
Copyright (c) 2026. Released under Apache 2.0.
The actual canonical free bar diagram of singular topological simplices.
Uses Mathlib's composable-arrow nerve (Joël Riou) and comma categories.
No bar augmentation equivalence or CW descent is assumed.
-/
import CWComparison.DerivedSimplexIntegral
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits Opposite LightCondensed LightCondensed.Solid
open scoped Simplicial

namespace CWComparison

/-- Ordinal action without reducing through bundled `Cat` objects. -/
abbrev barOrdinalFunctor {m n : SimplexCategory} (f : m ⟶ n) :
    Fin (m.len + 1) ⥤ Fin (n.len + 1) := f.toOrderHom.monotone.functor

/-- The actual category of continuous singular simplices and simplex operators. -/
abbrev singularSimplexCategory (X : TopCat) :=
  CostructuredArrow SimplexCategory.toTop X

/-- The coefficient diagram keeps the topology of each standard simplex. -/
abbrev singularFreeSimplexDiagram (X : TopCat) : singularSimplexCategory X ⥤ LightCondAb :=
  CostructuredArrow.proj SimplexCategory.toTop X ⋙
    SimplexCategory.toTop ⋙ freeLightCondAbOfTopFunctor

/-- Every finite string of singular simplices contributes the genuine free
object on its initial simplex, with no discreteness or projectivity claim. -/
abbrev singularFreeBarTerm (X : TopCat) (n : ℕ) : LightCondAb :=
  ∐ fun c : ComposableArrows (singularSimplexCategory X) n =>
    (singularFreeSimplexDiagram X).obj c.left

/-- All simplicial operators, including the nontrivial initial face, use the
actual free map on the intervening topological simplex operator. -/
def singularFreeBarMap (X : TopCat) {m n : SimplexCategoryᵒᵖ} (f : m ⟶ n) :
    singularFreeBarTerm X m.unop.len ⟶ singularFreeBarTerm X n.unop.len :=
  Sigma.desc (fun c : ComposableArrows (singularSimplexCategory X) m.unop.len =>
    (singularFreeSimplexDiagram X).map
      (c.map (homOfLE (Fin.zero_le ((barOrdinalFunctor f.unop).obj 0)))) ≫
        Sigma.ι (fun d : ComposableArrows (singularSimplexCategory X) n.unop.len =>
          (singularFreeSimplexDiagram X).obj d.left)
            (c.whiskerLeft (barOrdinalFunctor f.unop)))

/-- The complete free simplicial replacement, in every bar degree. -/
def singularFreeBar (X : TopCat) : SimplicialObject LightCondAb where
  obj n := singularFreeBarTerm X n.unop.len
  map f := singularFreeBarMap X f
  map_id n := by
    apply Sigma.hom_ext
    intro c
    simp only [singularFreeBarMap, Sigma.ι_comp_desc, Category.comp_id]
    change (singularFreeSimplexDiagram X).map (c.map (𝟙 (0 : Fin (n.unop.len + 1)))) ≫
      Sigma.ι (fun d : ComposableArrows (singularSimplexCategory X) n.unop.len =>
        (singularFreeSimplexDiagram X).obj d.left) c = _
    rw [c.map_id, (singularFreeSimplexDiagram X).map_id, Category.id_comp]
  map_comp f g := by
    apply Sigma.hom_ext
    intro c
    simp only [singularFreeBarMap, Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc, Category.assoc]
    rw [← Category.assoc, ← Functor.map_comp]
    change _ = (singularFreeSimplexDiagram X).map (c.map _ ≫ c.map _) ≫ _
    erw [← c.map_comp]
    rfl

/-- Evaluation in the target space is an actual cocone on the coefficient
diagram, before deriving or solidifying anything. -/
def singularFreeSimplexCocone (X : TopCat) : Cocone (singularFreeSimplexDiagram X) where
  pt := freeLightCondAbOfTopFunctor.obj X
  ι := {
    app c := freeLightCondAbOfTopFunctor.map c.hom
    naturality _ _ f := by
      change freeLightCondAbOfTopFunctor.map (SimplexCategory.toTop.map f.left) ≫
        freeLightCondAbOfTopFunctor.map _ = freeLightCondAbOfTopFunctor.map _ ≫ 𝟙 _
      rw [Category.comp_id, ← Functor.map_comp, CostructuredArrow.w f] }

end CWComparison

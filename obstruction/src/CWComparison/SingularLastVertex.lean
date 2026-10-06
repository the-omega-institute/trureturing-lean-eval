/-
Copyright (c) 2026. Released under Apache 2.0.
The actual last-vertex simplicial map from the previously retained canonical
singular-simplex nerve to the EXACT protected singular simplicial set. It is
strictly natural for every continuous map. Its quasi-isomorphism is a separate
proof obligation; no equivalence or CW descent is assumed here.
Uses Mathlib's nerve, singular set and coproduct chain comparison (Joël Riou),
all Apache-2.0.
-/
import CWComparison.LastVertexOperator
import CWComparison.SingularBarCollapse
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.MapHomologicalComplex

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits Opposite LightCondensed LightCondensed.Solid AlgebraicTopology
open scoped Simplicial

namespace CWComparison

/-- Evaluate the final simplex on the actual transported last vertices of the
entire string. The target is Mathlib's original singular set, including ULift. -/
def singularLastVertexMap (X : TopCat) :
    nerve (singularSimplexCategory X) ⟶ TopCat.toSSet.obj X where
  app p := ↾fun c => ULift.up
    (SimplexCategory.toTop.map
      (lastVertexOperator (c ⋙ CostructuredArrow.proj SimplexCategory.toTop X)) ≫
        (c.obj (Fin.last p.unop.len)).hom)
  naturality {m n} f := by
    ext c
    apply ULift.ext
    let d : ComposableArrows SimplexCategory m.unop.len :=
      c ⋙ CostructuredArrow.proj SimplexCategory.toTop X
    let a := c.map (homOfLE (Fin.le_last (f.unop.toOrderHom (Fin.last n.unop.len))))
    change SimplexCategory.toTop.map
        (lastVertexOperator (ComposableArrows.whiskerLeft d f.unop.toOrderHom.monotone.functor)) ≫
          (c.obj (f.unop.toOrderHom (Fin.last n.unop.len))).hom =
      SimplexCategory.toTop.map f.unop ≫
        (SimplexCategory.toTop.map (lastVertexOperator d) ≫
          (c.obj (Fin.last m.unop.len)).hom)
    rw [← CostructuredArrow.w a, ← Category.assoc, ← Functor.map_comp]
    change SimplexCategory.toTop.map
        (lastVertexOperator (ComposableArrows.whiskerLeft d f.unop.toOrderHom.monotone.functor) ≫
          d.map (homOfLE (Fin.le_last (f.unop.toOrderHom (Fin.last n.unop.len))))) ≫ _ = _
    rw [lastVertexOperator_whisker, Functor.map_comp, Category.assoc]

/-- Strict naturality holds before choosing any CW decomposition or deriving. -/
theorem singularLastVertexMap_naturality {X Y : TopCat} (f : X ⟶ Y) :
    nerveMap (CostructuredArrow.map f) ≫ singularLastVertexMap Y =
      singularLastVertexMap X ≫ TopCat.toSSet.map f := by
  ext p c
  apply ULift.ext
  change SimplexCategory.toTop.map
      (lastVertexOperator (c ⋙ CostructuredArrow.proj SimplexCategory.toTop X)) ≫
        ((c.obj (Fin.last p.unop.len)).hom ≫ f) =
    (SimplexCategory.toTop.map
      (lastVertexOperator (c ⋙ CostructuredArrow.proj SimplexCategory.toTop X)) ≫
        (c.obj (Fin.last p.unop.len)).hom) ≫ f
  exact (Category.assoc _ _ _).symm

/-- The canonical last-vertex map on integral chains, in all degrees. -/
abbrev singularNerveIntegralComparison (X : TopCat) :
    (nerve (singularSimplexCategory X)).chainComplex (ModuleCat.of ℤ ℤ) ⟶
      (((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
        (ModuleCat.of ℤ ℤ)).obj X) :=
  SSet.chainComplexMap (singularLastVertexMap X) (ModuleCat.of ℤ ℤ)

/-- The ordinary discrete nerve chains identify with the discrete image of
the original integral nerve chains by genuine coproduct preservation. -/
def singularDiscreteNerveChainsIso (X : TopCat) :
    (nerve (singularSimplexCategory X)).chainComplex
        ((LightCondensed.discrete (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)) ≅
      ((LightCondensed.discrete (ModuleCat ℤ)).mapHomologicalComplex (.down ℕ)).obj
        ((nerve (singularSimplexCategory X)).chainComplex (ModuleCat.of ℤ ℤ)) := by
  let F := LightCondensed.discrete (ModuleCat ℤ)
  haveI : F.IsLeftAdjoint := (LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).isLeftAdjoint
  haveI : F.Additive := Functor.additive_of_preserves_binary_products F
  exact ((SSet.chainComplexFunctorObjCompMapIso
    (LightCondensed.discrete (ModuleCat ℤ)) (ModuleCat.of ℤ ℤ)).app _).symm

/-- The target of this genuine chain map is the EXACT protected integral
singular complex. No alternative chain model is introduced. -/
def singularDiscreteNerveComparison (X : TopCat) :
    (nerve (singularSimplexCategory X)).chainComplex
        ((LightCondensed.discrete (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)) ⟶
      ((LightCondensed.discrete (ModuleCat ℤ)).mapHomologicalComplex (.down ℕ)).obj
        ((((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
          (ModuleCat.of ℤ ℤ)).obj X)) :=
  (singularDiscreteNerveChainsIso X).hom ≫
    ((LightCondensed.discrete (ModuleCat ℤ)).mapHomologicalComplex (.down ℕ)).map
      (singularNerveIntegralComparison X)

/-- The actual all-degree map, reindexed into the unbounded cochain category
by exactly the protected embedding. -/
abbrev singularDiscreteNerveUnboundedComparison (X : TopCat) :
    (((nerve (singularSimplexCategory X)).chainComplex
      ((LightCondensed.discrete (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ))).extend
        ComplexShape.embeddingDownNat) ⟶
      singularChainsLightCondAbComplexFunctor.obj X :=
  HomologicalComplex.extendMap (singularDiscreteNerveComparison X)
    ComplexShape.embeddingDownNat

end CWComparison

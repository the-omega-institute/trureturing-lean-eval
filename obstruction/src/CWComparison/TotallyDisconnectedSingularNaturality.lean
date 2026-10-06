/-
Copyright (c) 2026. Released under Apache 2.0.
Naturality of the pinned exact singular-chain computation for totally
disconnected spaces. Existing Mathlib chain models and computations are reused.
Mathlib sources by Johan Commelin, Kim Morrison, Adam Topaz, Andrew Yang and
Joël Riou, all Apache-2.0.
-/
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.QuasiIso

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits Opposite AlgebraicTopology
open scoped Simplicial

namespace CWComparison

/-- The inverse of the library's exact singular-set isomorphism commutes
with every map of totally disconnected spaces. It sends points to the actual
constant topological singular simplex, with the original ULift convention. -/
theorem totallyDisconnectedSingularSet_inv_naturality
    {X Y : TopCat.{0}} [TotallyDisconnectedSpace X] [TotallyDisconnectedSpace Y]
    (f : X ⟶ Y) :
    (TopCat.toSSetIsoConst X).inv ≫ TopCat.toSSet.map f =
      (Functor.const SimplexCategoryᵒᵖ).map (↾fun x : X => f x) ≫
        (TopCat.toSSetIsoConst Y).inv := by
  ext n x
  change X at x
  apply ULift.ext
  change TopCat.ofHom (X := SimplexCategory.toTop.obj n.unop) (Y := X)
      (ContinuousMap.const _ x) ≫ f =
    TopCat.ofHom (X := SimplexCategory.toTop.obj n.unop) (Y := Y)
      (ContinuousMap.const _ (f x))
  rfl

/-- Full chain-degree naturality of the exact library computation. -/
theorem totallyDisconnectedSingularChainIso_naturality
    {X Y : TopCat.{0}} [TotallyDisconnectedSpace X] [TotallyDisconnectedSpace Y]
    (f : X ⟶ Y) :
    (singularChainComplexFunctorIsoOfTotallyDisconnectedSpace
      (ModuleCat.{0} ℤ) (ModuleCat.of ℤ ℤ) X).inv ≫
        (((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)).map f) =
      ChainComplex.alternatingConst.map
        ((sigmaConst.obj (ModuleCat.of ℤ ℤ)).map (↾fun x : X => f x)) ≫
      (singularChainComplexFunctorIsoOfTotallyDisconnectedSpace
        (ModuleCat.{0} ℤ) (ModuleCat.of ℤ ℤ) Y).inv := by
  have h := totallyDisconnectedSingularSet_inv_naturality f
  let F := (SSet.chainComplexFunctor (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)
  have hh := congrArg F.map h
  simp only [Functor.map_comp] at hh
  apply HomologicalComplex.hom_ext
  intro n
  have hhn := congrArg (fun a => a.f n) hh
  simpa [F, singularChainComplexFunctorIsoOfTotallyDisconnectedSpace,
    singularChainComplexFunctor, SSet.chainComplexFunctor,
    alternatingFaceMapComplexConst, Functor.constComp] using hhn

/-- The exact protected integral singular chains are genuinely homotopy
equivalent to the degree-zero coproduct on points for a totally disconnected
space. All chain degrees, including the degenerate simplices, are contracted. -/
def totallyDisconnectedSingularIntegralHomotopyEquiv
    (X : TopCat.{0}) [TotallyDisconnectedSpace X] :
    HomotopyEquiv
      (((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)).obj X)
      ((ChainComplex.single₀ (ModuleCat.{0} ℤ)).obj
        ((sigmaConst.obj (ModuleCat.of ℤ ℤ)).obj X)) :=
  (HomotopyEquiv.ofIso
    (singularChainComplexFunctorIsoOfTotallyDisconnectedSpace
      (ModuleCat.{0} ℤ) (ModuleCat.of ℤ ℤ) X)).trans
    (ChainComplex.alternatingConstHomotopyEquiv _)

theorem totallyDisconnectedSingularIntegralAugmentation_quasiIso
    (X : TopCat.{0}) [TotallyDisconnectedSpace X] :
    QuasiIso (totallyDisconnectedSingularIntegralHomotopyEquiv X).hom :=
  (totallyDisconnectedSingularIntegralHomotopyEquiv X).quasiIso_hom

end CWComparison

/-
Copyright (c) 2026. Released under Apache 2.0.
Actual all-degree horizontal fiber contractions for the category-of-simplices
resolution. The fiber over a singular simplex tau is the genuine comma category
Under(tau), with its actual initial object (tau,id). No nerve comparison is a
premise. Mathlib's extra-degeneracy homotopy equivalence (Joël Riou) is reused.
-/
import CWComparison.SingularFiberContraction
import CWComparison.SingularFreeBar
import Mathlib.CategoryTheory.Limits.Comma
import Mathlib.Algebra.Homology.QuasiIso

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits Opposite AlgebraicTopology

namespace CWComparison

/-- The actual horizontal replacement fiber over a singular simplex. -/
abbrev singularResolutionFiber (X : TopCat) (τ : singularSimplexCategory X) := Under τ

/-- The integral augmented nerve of the actual fiber. -/
abbrev singularFiberIntegralAugmented (X : TopCat) (τ : singularSimplexCategory X) :=
  ((SimplicialObject.Augmented.whiskering (Type) (ModuleCat ℤ)).obj
    (sigmaConst.obj (ModuleCat.of ℤ ℤ))).obj
      (initialNerveAugmented (singularResolutionFiber X τ))

/-- The actual prepend-(tau,id) contraction, in all bar degrees. -/
def singularFiberIntegralExtraDegeneracy (X : TopCat) (τ : singularSimplexCategory X) :
    SimplicialObject.Augmented.ExtraDegeneracy (singularFiberIntegralAugmented X τ) :=
  (initialNerveExtraDegeneracy (singularResolutionFiber X τ)).map
    (sigmaConst.obj (ModuleCat.of ℤ ℤ))

/-- A genuine all-degree chain homotopy equivalence on each actual fiber.
The one-point coproduct is kept here as the exact augmentation target. -/
def singularFiberIntegralHomotopyEquiv (X : TopCat) (τ : singularSimplexCategory X) :
    HomotopyEquiv
      ((nerve (singularResolutionFiber X τ)).chainComplex (ModuleCat.of ℤ ℤ))
      ((ChainComplex.single₀ (ModuleCat ℤ)).obj
        ((sigmaConst.obj (ModuleCat.of ℤ ℤ)).obj PUnit)) :=
  (singularFiberIntegralExtraDegeneracy X τ).homotopyEquiv

/-- Its forward map is the actual augmented alternating-face map. -/
theorem singularFiberIntegralHomotopyEquiv_hom (X : TopCat)
    (τ : singularSimplexCategory X) :
    (singularFiberIntegralHomotopyEquiv X τ).hom =
      AlternatingFaceMapComplex.ε.app (singularFiberIntegralAugmented X τ) := rfl

/-- The actual horizontal fiber augmentation is a quasi-isomorphism in EVERY
chain degree. This is a proved contraction, not a comparison assumption. -/
theorem singularFiberIntegralAugmentation_quasiIso (X : TopCat)
    (τ : singularSimplexCategory X) :
    QuasiIso (AlternatingFaceMapComplex.ε.app (singularFiberIntegralAugmented X τ)) :=
  (singularFiberIntegralHomotopyEquiv X τ).quasiIso_hom

end CWComparison

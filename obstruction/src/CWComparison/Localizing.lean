/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in src/licenses/LICENSE.LeanCondensed.
-/
import CWComparison.FreeAugmentation
import CWComparison.SingularProjective
import CWComparison.DerivedMap
import CWComparison.DerivedLocalization

noncomputable section
open CategoryTheory Limits LightCondensed MonoidalCategory MonoidalClosed Opposite
open LightProfinite OnePoint

namespace CWComparison

/-- Continuous maps into the topological point form the terminal light condensed set. -/
def pointCondTerminal : IsTerminal point.toLightCondSet := by
  letI : topCatToLightCondSet.IsRightAdjoint :=
    LightCondSet.topCatAdjunction.isRightAdjoint
  exact TopCat.isTerminalPUnit.isTerminalObj topCatToLightCondSet _

/-- The actual monoidal unit is discrete integers, with no change of solidness. -/
def tensorUnitIsoInt : 𝟙_ LightCondAb ≅
    (LightCondensed.discrete (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ) :=
  Functor.Monoidal.εIso (free ℤ) ≪≫
    (free ℤ).mapIso (pointCondTerminal.uniqueUpToIso
      SemiCartesianMonoidalCategory.isTerminalTensorUnit).symm ≪≫ freePointIsoInt

instance tensorUnit_projective : Projective (𝟙_ LightCondAb) :=
  Projective.of_iso tensorUnitIsoInt.symm (discrete_projective (ModuleCat.of ℤ ℤ))

/-- Internal projectivity implies actual projectivity here because the tensor unit
is projective. This uses the proved epimorphism preservation at the point. -/
theorem projective_of_internallyProjective (A : LightCondAb) [InternallyProjective A] :
    Projective A :=
  Projective.of_iso (ρ_ A) ((ihom.adjunction A).map_projective (𝟙_ LightCondAb) inferInstance)

/-- The protected localization source is a genuine projective object. -/
instance P_projective : Projective P := projective_of_internallyProjective P

/-- The free convergent-sequence object is genuinely projective as well. -/
instance freeSequence_projective : Projective ((free ℤ).obj (ℕ∪{∞}).toCondensed) :=
  projective_of_internallyProjective _

/-- The protected solidness condition gives the actual Hom bijection for every
light profinite parameter, not only for the point. -/
theorem solid_pre_tensor_bijective (S : LightProfinite) (A : LightCondensed.Solid) :
    Function.Bijective (fun (g : P ⊗ (free ℤ).obj S.toCondensed ⟶ A.obj) =>
      (oneMinusShift ▷ (free ℤ).obj S.toCondensed) ≫ g) := by
  have : IsIso ((MonoidalClosed.pre oneMinusShift).app A.obj) := A.property
  let e := ihomPoints ℤ P A.obj S
  exact bijective_conjugate e
    (fun x => (((MonoidalClosed.pre oneMinusShift).app A.obj).hom.app (op S)) x)
    (fun g => (oneMinusShift ▷ (free ℤ).obj S.toCondensed) ≫ g)
    (fun x => ReflectionProof.ihomPoints_pre_app oneMinusShift S x)
    (ConcreteCategory.bijective_of_isIso _)

/-- The genuine reflector inverts every defining solid localization map. -/
theorem solidification_tensor_oneMinusShift_isIso (S : LightProfinite) :
    IsIso (LightCondensed.Solid.solidification.map
      (oneMinusShift ▷ (free ℤ).obj S.toCondensed)) := by
  apply isIso_of_coyoneda_map_bijective
  intro A
  let e := LightCondensed.Solid.solidificationAdjunction.homEquiv
    (P ⊗ (free ℤ).obj S.toCondensed) A
  exact bijective_conjugate e.symm
    (fun g => (oneMinusShift ▷ (free ℤ).obj S.toCondensed) ≫ g)
    (fun g => LightCondensed.Solid.solidification.map
      (oneMinusShift ▷ (free ℤ).obj S.toCondensed) ≫ g)
    (fun g => LightCondensed.Solid.solidificationAdjunction.homEquiv_naturality_left_symm
      (oneMinusShift ▷ (free ℤ).obj S.toCondensed) g)
    (solid_pre_tensor_bijective S A)

end CWComparison

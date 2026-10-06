/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in src/licenses/LICENSE.LeanCondensed.
-/
import CWComparison.Localizing
import CWComparison.SingularDerived

noncomputable section
open CategoryTheory Limits LightCondensed LightCondensed.Solid MonoidalCategory
open LightProfinite OnePoint

namespace CWComparison

/-- The free condensed group on the monoidal point is the actual tensor unit. -/
def freeProfinitePointUnitIso :
    (free ℤ).obj (𝟙_ LightProfinite).toCondensed ≅ 𝟙_ LightCondAb :=
  (Functor.Monoidal.εIso (lightProfiniteToLightCondSet ⋙ free ℤ)).symm

/-- Removing the free-point tensor factor. -/
def PPointTensorIso : P ⊗ (free ℤ).obj (𝟙_ LightProfinite).toCondensed ≅ P :=
  (Iso.refl P ⊗ᵢ freeProfinitePointUnitIso) ≪≫ ρ_ P

/-- The original reflector inverts the exact protected `oneMinusShift`. -/
theorem solidification_oneMinusShift_isIso : IsIso (solidification.map oneMinusShift) := by
  have : IsIso (solidification.map
      (oneMinusShift ▷ (free ℤ).obj (𝟙_ LightProfinite).toCondensed)) :=
    solidification_tensor_oneMinusShift_isIso (𝟙_ LightProfinite)
  have hn : (oneMinusShift ▷ (free ℤ).obj (𝟙_ LightProfinite).toCondensed) ≫
      PPointTensorIso.hom = PPointTensorIso.hom ≫ oneMinusShift := by
    dsimp [PPointTensorIso]
    simp only [id_tensorHom, Category.assoc]
    rw [← whisker_exchange_assoc, MonoidalCategory.rightUnitor_naturality]
  have hf : oneMinusShift = PPointTensorIso.inv ≫
      (oneMinusShift ▷ (free ℤ).obj (𝟙_ LightProfinite).toCondensed) ≫
        PPointTensorIso.hom := by
    rw [hn, Iso.inv_hom_id_assoc]
  rw [hf, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  infer_instance

/-- The actual degree-zero localization source is K-projective in the full
unbounded complex category. -/
instance P_single_isKProjective : CochainComplex.IsKProjective
    ((CochainComplex.singleFunctor LightCondAb 0).obj P) :=
  CochainComplex.isKProjective_of_projective _ 0

/-- Actual derived solidification inverts the protected localization map in degree
zero. The only outstanding premise is the separately owned derived adjunction. -/
theorem totalDerived_oneMinusShift_isIso
    [solidificationComplexQ.HasLeftDerivedFunctor
      (HomologicalComplex.quasiIso LightCondAb (.up ℤ))]
    (adj : totalDerivedSolidification ⊣ derivedInclusion) :
    IsIso (totalDerivedSolidification.map
      ((DerivedCategory.singleFunctor LightCondAb 0).map oneMinusShift)) := by
  have : IsIso (solidification.map oneMinusShift) := solidification_oneMinusShift_isIso
  have : IsIso ((solidification.mapHomologicalComplex (.up ℤ)).map
      ((CochainComplex.singleFunctor LightCondAb 0).map oneMinusShift)) := by
    apply (NatIso.isIso_map_iff
      (HomologicalComplex.singleMapHomologicalComplex solidification (.up ℤ) 0)
      oneMinusShift).2
    change IsIso ((CochainComplex.singleFunctor Solid 0).map
      (solidification.map oneMinusShift))
    infer_instance
  have : IsIso ((solidification.mapHomotopyCategory (.up ℤ)).map
      ((HomotopyCategory.quotient LightCondAb (.up ℤ)).map
        ((CochainComplex.singleFunctor LightCondAb 0).map oneMinusShift))) := by
    rw [Functor.mapHomotopyCategory_map]
    infer_instance
  exact derivedAdjunction_map_isIso solidificationAdjunction adj
    ((CochainComplex.singleFunctor LightCondAb 0).obj P)
    ((CochainComplex.singleFunctor LightCondAb 0).map oneMinusShift)

end CWComparison

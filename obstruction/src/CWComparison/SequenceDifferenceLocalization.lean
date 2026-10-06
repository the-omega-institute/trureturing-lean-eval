/-
Copyright (c) 2026. Released under Apache 2.0.
The actual identity-minus-successor-plus-infinity map on the protected free
convergent sequence. Its inversion is a consequence of the already proved
protected P localization and the actual split presentation, not a new premise.
Uses Mathlib short-complex splittings (Joël Riou), Apache-2.0.
-/
import CWComparison.BinaryShift
import CWComparison.DerivedTensorInversion
import CWComparison.ShiftDerived

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits LightCondensed LightCondensed.Solid LightProfinite OnePoint
open MonoidalCategory

namespace CWComparison

/-- The actual constant map at the limit point, in the protected light site. -/
def sequenceInfinity : ℕ∪{∞} ⟶ ℕ∪{∞} :=
  ι_split.retraction ≫ ι

/-- This is a sum of maps of the actual free topological sequence. It acts
as identity on the infinity summand and as protected oneMinusShift on P. -/
def freeSequenceDifference :
    (free ℤ).obj (ℕ∪{∞}).toCondensed ⟶ (free ℤ).obj (ℕ∪{∞}).toCondensed :=
  𝟙 _ - (lightProfiniteToLightCondSet ⋙ free ℤ).map LightProfinite.shift +
    (lightProfiniteToLightCondSet ⋙ free ℤ).map sequenceInfinity

theorem freeSequenceDifference_retraction :
    freeSequenceDifference ≫ PSequence_split.r = PSequence_split.r := by
  change freeSequenceDifference ≫
    (lightProfiniteToLightCondSet ⋙ free ℤ).map ι_split.retraction =
      (lightProfiniteToLightCondSet ⋙ free ℤ).map ι_split.retraction
  simp only [freeSequenceDifference, Preadditive.add_comp, Preadditive.sub_comp,
    Category.id_comp, ← Functor.map_comp]
  have h₁ : LightProfinite.shift ≫ ι_split.retraction = ι_split.retraction := rfl
  have h₂ : sequenceInfinity ≫ ι_split.retraction = ι_split.retraction := rfl
  rw [h₁, h₂]
  simp

theorem freeSequenceDifference_projection :
    freeSequenceDifference ≫ P_proj = P_proj ≫ oneMinusShift := by
  simp only [freeSequenceDifference, Preadditive.add_comp, Preadditive.sub_comp,
    Category.id_comp]
  have h : (lightProfiniteToLightCondSet ⋙ free ℤ).map sequenceInfinity ≫ P_proj = 0 := by
    simp only [sequenceInfinity, Functor.map_comp, Category.assoc]
    change _ ≫ P_map ≫ cokernel.π P_map = 0
    simp
  rw [h, add_zero, oneMinusShift_eq, Preadditive.comp_sub, Category.comp_id,
    P_proj_sequencePMap]
  rfl

/-- The block decomposition is proved against the exact protected splitting. -/
theorem freeSequenceDifference_split :
    freeSequenceDifference =
      (PSequence_split.r ≫ P_map : (free ℤ).obj (ℕ∪{∞}).toCondensed ⟶
        (free ℤ).obj (ℕ∪{∞}).toCondensed) +
      (P_proj ≫ oneMinusShift ≫ PSequence_split.s :
        (free ℤ).obj (ℕ∪{∞}).toCondensed ⟶ (free ℤ).obj (ℕ∪{∞}).toCondensed) := by
  calc
    freeSequenceDifference = freeSequenceDifference ≫
        ((PSequence_split.r ≫ P_map : (free ℤ).obj (ℕ∪{∞}).toCondensed ⟶
          (free ℤ).obj (ℕ∪{∞}).toCondensed) +
         (P_proj ≫ PSequence_split.s : (free ℤ).obj (ℕ∪{∞}).toCondensed ⟶
          (free ℤ).obj (ℕ∪{∞}).toCondensed)) := by
      change _ = _ ≫ (PSequence_split.r ≫ PSequence.f + PSequence.g ≫ PSequence_split.s)
      rw [PSequence_split.id, Category.comp_id]
    _ = _ := by
      rw [Preadditive.comp_add, ← Category.assoc, freeSequenceDifference_retraction,
        ← Category.assoc, freeSequenceDifference_projection, Category.assoc]

/-- The genuine derived left adjoint inverts the exact protected P map.
This removes the actual free-point tensor parameter in the retained theorem. -/
theorem derivedAdjunction_oneMinusShift_isIso
    {L : DLightCondAb ⥤ DSolid} (adj : L ⊣ derivedInclusion) (n : ℤ) :
    IsIso (L.map ((DerivedCategory.singleFunctor LightCondAb n).map oneMinusShift)) := by
  let D := DerivedCategory.singleFunctor LightCondAb n ⋙ L
  haveI : IsIso (D.map
      (oneMinusShift ▷ (free ℤ).obj (𝟙_ LightProfinite).toCondensed)) :=
    derivedAdjunction_tensor_oneMinusShift_isIso adj _ n
  have hn : (oneMinusShift ▷ (free ℤ).obj (𝟙_ LightProfinite).toCondensed) ≫
      PPointTensorIso.hom = PPointTensorIso.hom ≫ oneMinusShift := by
    dsimp [PPointTensorIso]
    simp only [id_tensorHom, Category.assoc]
    rw [← whisker_exchange_assoc, MonoidalCategory.rightUnitor_naturality]
  have hf : oneMinusShift = PPointTensorIso.inv ≫
      (oneMinusShift ▷ (free ℤ).obj (𝟙_ LightProfinite).toCondensed) ≫
        PPointTensorIso.hom := by
    rw [hn, Iso.inv_hom_id_assoc]
  change IsIso (D.map oneMinusShift)
  rw [hf, D.map_comp, D.map_comp]
  infer_instance

/-- The actual full unbounded derived left adjoint inverts the linear
combination of free continuous maps, in EVERY integer placement. -/
theorem derivedFreeSequenceDifference_isIso
    {L : DLightCondAb ⥤ DSolid} (adj : L ⊣ derivedInclusion) (n : ℤ) :
    IsIso (L.map ((DerivedCategory.singleFunctor LightCondAb n).map
      freeSequenceDifference)) := by
  haveI : L.Additive := adj.left_adjoint_additive
  let D := DerivedCategory.singleFunctor LightCondAb n ⋙ L
  let s := PSequence_split.map D
  haveI : IsIso (D.map oneMinusShift) := derivedAdjunction_oneMinusShift_isIso adj n
  have he : D.map freeSequenceDifference =
      s.r ≫ (PSequence.map D).f + (PSequence.map D).g ≫
        D.map oneMinusShift ≫ s.s := by
    simpa only [s, ShortComplex.Splitting.map_r, ShortComplex.Splitting.map_s,
      ShortComplex.map_f, ShortComplex.map_g, PSequence,
      Functor.map_add, Functor.map_comp] using
      congrArg D.map freeSequenceDifference_split
  change IsIso (D.map freeSequenceDifference)
  rw [he]
  refine ⟨⟨s.r ≫ (PSequence.map D).f + (PSequence.map D).g ≫
    inv (D.map oneMinusShift) ≫ s.s, ?_, ?_⟩⟩ <;>
    simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc,
      s.f_r_assoc, (PSequence.map D).zero_assoc, s.s_r_assoc, s.s_g_assoc,
      IsIso.hom_inv_id_assoc, IsIso.inv_hom_id_assoc, Category.comp_id,
      comp_zero, zero_comp, add_zero, zero_add, s.id] <;> rfl

end CWComparison

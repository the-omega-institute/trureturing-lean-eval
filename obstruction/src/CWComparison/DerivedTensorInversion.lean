/-
Copyright (c) 2026. Released under Apache 2.0.
Actual inversion of the protected localization map by the derived adjoint.
Only genuine unbounded derived construction/adjunction are external premises.
-/
import CWComparison.FrozenTensorOrthogonality
import CWComparison.TensorLocalization
import CWComparison.SingularDerived

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits LightCondensed LightCondensed.Solid MonoidalCategory

namespace CWComparison

/-- The genuine derived left adjoint inverts `oneMinusShift` with every
condensed tensor parameter, placed in every integer degree. The full unbounded
right-hand locality and exact mate calculation come from the frozen supplier. -/
theorem derivedAdjunction_tensor_oneMinusShift_isIso
    {L : DLightCondAb ⥤ DSolid} (adj : L ⊣ derivedInclusion)
    (B : LightCondAb) (n : ℤ) :
    IsIso (L.map ((DerivedCategory.singleFunctor LightCondAb n).map
      (oneMinusShift ▷ B))) := by
  apply isIso_of_coyoneda_map_bijective
  intro Y
  haveI := solidDerivedEndomorphism_derivedInclusion_isIso Y
  let e := adj.homEquiv ((DerivedCategory.singleFunctor LightCondAb n).obj (P ⊗ B)) Y
  exact bijective_conjugate e.symm _ _
    (fun g => adj.homEquiv_naturality_left_symm
      ((DerivedCategory.singleFunctor LightCondAb n).map (oneMinusShift ▷ B)) g)
    (solidTensorSingle_precomp_bijective B n (derivedInclusion.obj Y))

/-- Specialization to Mathlib's actual total-left-derived construction of the
protected reflector, with only its separately owned existence and adjunction. -/
theorem totalDerived_tensor_oneMinusShift_isIso
    [solidificationComplexQ.HasLeftDerivedFunctor
      (HomologicalComplex.quasiIso LightCondAb (.up ℤ))]
    (adj : totalDerivedSolidification ⊣ derivedInclusion)
    (B : LightCondAb) (n : ℤ) :
    IsIso (totalDerivedSolidification.map
      ((DerivedCategory.singleFunctor LightCondAb n).map (oneMinusShift ▷ B))) :=
  derivedAdjunction_tensor_oneMinusShift_isIso adj B n

end CWComparison

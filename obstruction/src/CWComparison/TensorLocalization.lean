/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in src/licenses/LICENSE.LeanCondensed.
-/
import CWComparison.Localizing

noncomputable section
open CategoryTheory Limits LightCondensed MonoidalCategory MonoidalClosed

namespace CWComparison

/-- Internal solidness controls the defining map tensored with any actual
light condensed group, including the free interval and free simplices. -/
theorem solid_pre_tensor_any_bijective (B : LightCondAb) (A : LightCondensed.Solid) :
    Function.Bijective (fun (g : P ⊗ B ⟶ A.obj) => (oneMinusShift ▷ B) ≫ g) := by
  let k := (MonoidalClosed.pre oneMinusShift).app A.obj
  have : IsIso k := A.property
  have hk : Function.Bijective (fun (g : B ⟶ (ihom P).obj A.obj) => g ≫ k) := by
    constructor
    · intro g h w
      exact (cancel_mono k).mp w
    · intro g
      exact ⟨g ≫ inv k, by simp⟩
  exact bijective_conjugate ((ihom.adjunction P).homEquiv B A.obj).symm
    (fun g => g ≫ k) (fun g => (oneMinusShift ▷ B) ≫ g)
    (fun g => MonoidalClosed.uncurry_pre_app A.obj g oneMinusShift) hk

/-- The genuine reflector inverts the defining localization map with every
light condensed tensor parameter. No free-object homotopy invariance is assumed. -/
theorem solidification_tensor_any_oneMinusShift_isIso (B : LightCondAb) :
    IsIso (LightCondensed.Solid.solidification.map (oneMinusShift ▷ B)) := by
  apply isIso_of_coyoneda_map_bijective
  intro A
  let e := LightCondensed.Solid.solidificationAdjunction.homEquiv (P ⊗ B) A
  exact bijective_conjugate e.symm
    (fun g => (oneMinusShift ▷ B) ≫ g)
    (fun g => LightCondensed.Solid.solidification.map (oneMinusShift ▷ B) ≫ g)
    (fun g => LightCondensed.Solid.solidificationAdjunction.homEquiv_naturality_left_symm
      (oneMinusShift ▷ B) g)
    (solid_pre_tensor_any_bijective B A)

end CWComparison

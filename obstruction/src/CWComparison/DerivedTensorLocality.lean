/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in src/licenses/LICENSE.LeanCondensed.
-/
import CWComparison.FrozenFreeFlat

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits LightCondensed LightCondensed.Solid MonoidalCategory MonoidalClosed

namespace CWComparison

/-- The exact internal-Hom localization map is invertible on the actual derived
inclusion of every unbounded solid complex. This is a proved right-hand input to
the supplied derived tensor adjunction, not a free-object acyclicity assumption. -/
theorem derivedPreP_solid_isIso (Y : DSolid) :
    IsIso ((MonoidalClosed.pre oneMinusShift).mapDerivedCategory.app
      (derivedInclusion.obj Y)) := by
  let K := DerivedCategory.Q.objPreimage Y
  let T := (isSolid.ι.mapHomologicalComplex (.up ℤ)).obj K
  let e : DerivedCategory.Q.obj T ≅ derivedInclusion.obj Y :=
    (isSolid.ι.mapDerivedCategoryFactors.app K).symm ≪≫
      derivedInclusion.mapIso (DerivedCategory.Q.objObjPreimageIso Y)
  rw [← NatTrans.isIso_app_iff_of_iso (MonoidalClosed.pre oneMinusShift).mapDerivedCategory e]
  let p := ((MonoidalClosed.pre oneMinusShift).mapHomologicalComplex (.up ℤ)).app T
  haveI : ∀ n : ℤ, IsIso (p.f n) := fun n => (K.X n).property
  haveI : IsIso p := HomologicalComplex.Hom.isIso_of_components p
  rw [NatTrans.mapDerivedCategory_app_Q_obj]
  infer_instance

end CWComparison

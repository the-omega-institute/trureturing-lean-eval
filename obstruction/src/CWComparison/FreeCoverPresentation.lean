/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in src/licenses/LICENSE.LeanCondensed.

Uses the effective-epimorphism/kernel-pair API by Adam Topaz and the
light-condensed sheaf API by Dagur Asgeirsson.
-/
import CWComparison.ProfiniteCover
import Mathlib.Condensed.Light.EffectiveEpi

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits LightCondensed

namespace CWComparison

variable {T : LightProfinite} {X : TopCat} [T2Space X]

/-- The actual topological relation space of the covering, which is light profinite. -/
def coverRelationTopIso (f : C(T, X)) :
    (coverPullback f f).toTop ≅ (TopCat.pullbackCone (TopCat.ofHom f) (TopCat.ofHom f)).pt :=
  Iso.refl _

/-- The free relation cofork, using the exact protected free functor. -/
def freeCoverCofork (f : C(T, X)) :
    Cofork
      (LightCondensed.Solid.freeLightCondAbOfTopFunctor.map
        (TopCat.pullbackCone (TopCat.ofHom f) (TopCat.ofHom f)).fst)
      (LightCondensed.Solid.freeLightCondAbOfTopFunctor.map
        (TopCat.pullbackCone (TopCat.ofHom f) (TopCat.ofHom f)).snd) :=
  Cofork.ofπ (LightCondensed.Solid.freeLightCondAbOfTopFunctor.map (TopCat.ofHom f))
    (by
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg LightCondensed.Solid.freeLightCondAbOfTopFunctor.map
        (TopCat.pullbackCone (TopCat.ofHom f) (TopCat.ofHom f)).condition)

/-- The free covering object is the coequalizer of the actual two relation maps. -/
def freeCoverCoforkIsColimit (f : C(T, X)) (hf : Function.Surjective f) :
    IsColimit (freeCoverCofork f) := by
  letI : topCatToLightCondSet.IsRightAdjoint :=
    LightCondSet.topCatAdjunction.isRightAdjoint
  letI : Epi (topCatToLightCondSet.map (TopCat.ofHom f)) :=
    profiniteCover_condensed_epi (T := T) (X := X) f hf
  letI : EffectiveEpi (topCatToLightCondSet.map (TopCat.ofHom f)) :=
    (regularEpiOfEpi _).effectiveEpi
  let c := TopCat.pullbackCone (TopCat.ofHom f) (TopCat.ofHom f)
  let c' := PullbackCone.mk (topCatToLightCondSet.map c.fst)
    (topCatToLightCondSet.map c.snd)
    (by rw [← Functor.map_comp, ← Functor.map_comp]; exact congrArg _ c.condition)
  have hc' : IsLimit c' :=
    isLimitPullbackConeMapOfIsLimit topCatToLightCondSet c.condition
      (TopCat.pullbackConeIsLimit (TopCat.ofHom f) (TopCat.ofHom f))
  exact isColimitCoforkMapOfIsColimit (free ℤ) c'.condition
    (isColimitCoforkOfEffectiveEpi (topCatToLightCondSet.map (TopCat.ofHom f)) c' hc')

/-- The relation difference and cover augmentation form the genuine free presentation. -/
def freeCoverPresentation (f : C(T, X)) : ShortComplex LightCondAb :=
  ShortComplex.mk
    (LightCondensed.Solid.freeLightCondAbOfTopFunctor.map
        (TopCat.pullbackCone (TopCat.ofHom f) (TopCat.ofHom f)).fst -
      LightCondensed.Solid.freeLightCondAbOfTopFunctor.map
        (TopCat.pullbackCone (TopCat.ofHom f) (TopCat.ofHom f)).snd)
    (LightCondensed.Solid.freeLightCondAbOfTopFunctor.map (TopCat.ofHom f))
    (by
      rw [Preadditive.sub_comp, sub_eq_zero]
      exact (freeCoverCofork f).condition)

/-- Exactness at the free covering object, without assuming any derived acyclicity. -/
theorem freeCoverPresentation_exact (f : C(T, X)) (hf : Function.Surjective f) :
    (freeCoverPresentation f).Exact := by
  apply ShortComplex.exact_of_g_is_cokernel
  exact Preadditive.isColimitCokernelCoforkOfCofork (freeCoverCoforkIsColimit f hf)

/-- The binary Cantor relation gives an unconditional presentation of the free interval. -/
theorem binaryIntervalPresentation_exact :
    (freeCoverPresentation (X := TopCat.of unitInterval) binaryIntervalCover).Exact :=
  freeCoverPresentation_exact (X := TopCat.of unitInterval)
    binaryIntervalCover Real.fromBinary_surjective

end CWComparison

/-
Copyright (c) 2026. Released under Apache 2.0.
Exact protected CW scope check and actual derived equivalences of the
functorial indiscrete thickening. Reuses the accepted free binary homotopy and
the exact protected singular prism. It assumes no CW comparison.
-/
import CWComparison.CWThickening
import CWComparison.DerivedFreeHomotopy
import CWComparison.SingularHomotopy

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits LightCondensed LightCondensed.Solid

namespace CWComparison

/-- EVERY TopCat object has the actual functorial thickening in the EXACT
protected CW full subcategory, using the proved classical zero-cell structure. -/
def cwThickeningCWFunctor : TopCat ⥤ CWTopCat where
  obj X := ⟨cwThickeningTopFunctor.obj X, ⟨thickeningCWComplex X⟩⟩
  map f := ObjectProperty.homMk (cwThickeningTopFunctor.map f)
  map_id _ := rfl
  map_comp _ _ := rfl

theorem cwThickeningCWFunctor_comp_inclusion :
    cwThickeningCWFunctor ⋙ CWTopCat.toTopCat = cwThickeningTopFunctor := rfl

/-- The actual derived free functor inverts the canonical projection from
the thickening, by the already-proved all-TopCat free homotopy theorem. -/
theorem derivedFreeThickeningProjection_isIso
    {L : DLightCondAb ⥤ DSolid} (adj : L ⊣ derivedInclusion) (X : TopCat) :
    IsIso ((freeLightCondAbOfTopFunctor ⋙ DerivedCategory.singleFunctor LightCondAb 0 ⋙ L).map
      (cwThickeningProjection.app X)) := by
  let D := freeLightCondAbOfTopFunctor ⋙ DerivedCategory.singleFunctor LightCondAb 0 ⋙ L
  change IsIso (D.map (cwThickeningProjection.app X))
  refine ⟨⟨D.map (cwThickeningSection.app X), ?_, ?_⟩⟩
  · rw [← D.map_comp]
    exact (derivedFreeMap_homotopy adj (cwThickeningHomotopy X)).trans (D.map_id _)
  · rw [← D.map_comp]
    change D.map (𝟙 X) = 𝟙 _
    exact D.map_id X

/-- These canonical projection maps form an actual natural equivalence on
all TopCat, with no comparison or descent premise. -/
def derivedFreeThickeningNatIso
    {L : DLightCondAb ⥤ DSolid} (adj : L ⊣ derivedInclusion) :
    cwThickeningTopFunctor ⋙
        (freeLightCondAbOfTopFunctor ⋙ DerivedCategory.singleFunctor LightCondAb 0 ⋙ L) ≅
      freeLightCondAbOfTopFunctor ⋙ DerivedCategory.singleFunctor LightCondAb 0 ⋙ L := by
  let D := freeLightCondAbOfTopFunctor ⋙ DerivedCategory.singleFunctor LightCondAb 0 ⋙ L
  let a := Functor.whiskerRight cwThickeningProjection D
  haveI : IsIso a := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact derivedFreeThickeningProjection_isIso adj
  exact asIso a ≪≫ Functor.leftUnitor D

/-- The protected singular chains also invert the same actual projection,
using their retained prism theorem in every chain degree. -/
theorem singularChainsThickeningProjection_isIso (X : TopCat) :
    IsIso (singularChainsSolidDerivedFunctor.map (cwThickeningProjection.app X)) := by
  let D := singularChainsSolidDerivedFunctor
  refine ⟨⟨D.map (cwThickeningSection.app X), ?_, ?_⟩⟩
  · rw [← D.map_comp]
    exact (singularChainsSolidDerived_map_eq_of_homotopy
      (cwThickeningHomotopy X)).trans (D.map_id _)
  · rw [← D.map_comp]
    change D.map (𝟙 X) = 𝟙 _
    exact D.map_id X

/-- A genuine natural projection equivalence for the EXACT solid lift of
protected singular chains, independently of any derived reflector. -/
def singularChainsThickeningNatIso :
    cwThickeningTopFunctor ⋙ singularChainsSolidDerivedFunctor ≅
      singularChainsSolidDerivedFunctor := by
  let a := Functor.whiskerRight cwThickeningProjection singularChainsSolidDerivedFunctor
  haveI : IsIso a := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact singularChainsThickeningProjection_isIso
  exact asIso a ≪≫ Functor.leftUnitor _

end CWComparison

/-
Copyright (c) 2026. Released under Apache 2.0.
Joint incompatibility certificate for the exact official holes 7, 9 and 10 of
derived_solidification_free_CW_homology. Reuses the audited protected natural
comparison obstruction and the original Mathlib/LeanCondensed definitions.
The raw official Challenge is statement evidence only and is not imported.
-/
import CWComparison.ProtectedCWComparisonObstruction

open CategoryTheory LightCondensed LightCondensed.Solid

namespace CWComparison

/-- No compatible choices of the official derived functor (hole 4), CW functor
(hole 8), genuine derived adjunction (hole 7), functor specification (hole 9)
and natural singular-chain comparison (hole 10) exist. This certifies joint
incompatibility, without assuming a derived construction or changing CW scope. -/
theorem official_holes7_9_10_joint_target_empty :
    ¬ ∃ (L : DLightCondAb ⥤ DSolid) (F : CWTopCat ⥤ DLightCondAb),
      Nonempty (L ⊣ derivedInclusion) ∧
      Nonempty (F ≅
        CWTopCat.toTopCat ⋙ freeLightCondAbOfTopFunctor ⋙
          DerivedCategory.singleFunctor LightCondAb 0 ⋙ L ⋙ derivedInclusion) ∧
      Nonempty (F ≅ singularChainsLightCondAbCWDerivedFunctor) := by
  rintro ⟨L, F, ⟨adj⟩, ⟨spec⟩, ⟨h10⟩⟩
  exact protectedCWComparison_not_nonempty adj ⟨spec.symm ≪≫ h10⟩

end CWComparison

/- Exact official joint-target type, protected-object and recursive axiom audit.
Released under Apache 2.0. No unfinished official Challenge is imported. -/

open CategoryTheory LightCondensed LightCondensed.Solid

#check CWComparison.official_holes7_9_10_joint_target_empty
#print axioms CWComparison.official_holes7_9_10_joint_target_empty

example : freeLightCondAbOfTopFunctor = topCatToLightCondSet ⋙ free ℤ := rfl

example : isCWTopCat = fun X : TopCat =>
    Nonempty (Topology.CWComplex (Set.univ : Set X)) := rfl

example : derivedInclusion = Functor.mapDerivedCategory isSolid.ι := rfl

example : singularChainsLightCondAbComplexFunctor =
    ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
      (ModuleCat.of ℤ ℤ)) ⋙
        (LightCondensed.discrete (ModuleCat ℤ)).mapHomologicalComplex (ComplexShape.down ℕ) ⋙
          ComplexShape.embeddingDownNat.extendFunctor LightCondAb := rfl

example : singularChainsLightCondAbDerivedFunctor =
    singularChainsLightCondAbComplexFunctor ⋙ DerivedCategory.Q := rfl

example : singularChainsLightCondAbCWDerivedFunctor =
    CWTopCat.toTopCat ⋙ singularChainsLightCondAbDerivedFunctor := rfl

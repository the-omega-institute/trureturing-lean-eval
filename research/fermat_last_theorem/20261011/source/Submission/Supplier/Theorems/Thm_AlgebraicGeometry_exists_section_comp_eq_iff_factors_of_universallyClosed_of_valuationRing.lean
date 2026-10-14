import Mathlib
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_AlgebraicGeometry_exists_section_comp_eq_iff_factors_of_universallyClosed_of_valuationRing

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_section_comp_eq_iff_factors_of_universallyClosed_of_valuationRing
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X Xf X' : Scheme.{u}} (g : X ⟶ Spec (.of R))
    (i : Xf ⟶ X) [IsOpenImmersion i] [UniversallyClosed (i ≫ g)]
    (j : X' ⟶ X)
    (hcover : Set.range i ∪ Set.range j = Set.univ)
    (hempty : IsLocalRing.closedPoint R ∉ Set.range (j ≫ g))
    (x : Spec (.of K) ⟶ X) (hx : x ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    (∃ s : Spec (.of R) ⟶ X, s ≫ g = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ s = x) ↔
      ∃ xf : Spec (.of K) ⟶ Xf, xf ≫ i = x := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_section_comp_eq_iff_factors_of_universallyClosed_of_valuationRing.solution

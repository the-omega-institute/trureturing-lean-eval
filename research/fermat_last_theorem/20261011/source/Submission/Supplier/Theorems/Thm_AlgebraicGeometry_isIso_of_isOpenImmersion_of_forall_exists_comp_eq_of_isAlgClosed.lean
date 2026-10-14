import Mathlib
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_AlgebraicGeometry_isIso_of_isOpenImmersion_of_forall_exists_comp_eq_of_isAlgClosed

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.isIso_of_isOpenImmersion_of_forall_exists_comp_eq_of_isAlgClosed
    {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
    {X Y : Scheme.{u}} (gY : Y ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType gY]
    (i : X ⟶ Y) [IsOpenImmersion i]
    (hsurj : ∀ y : Spec (CommRingCat.of Ω) ⟶ Y, y ≫ gY = Spec.map (CommRingCat.ofHom (algebraMap K Ω)) →
      ∃ x : Spec (CommRingCat.of Ω) ⟶ X, x ≫ i = y) :
    IsIso i := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isIso_of_isOpenImmersion_of_forall_exists_comp_eq_of_isAlgClosed.solution

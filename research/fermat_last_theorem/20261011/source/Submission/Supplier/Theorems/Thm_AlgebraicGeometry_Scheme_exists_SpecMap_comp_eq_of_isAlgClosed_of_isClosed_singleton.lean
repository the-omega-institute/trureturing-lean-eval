import Mathlib
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_AlgebraicGeometry_Scheme_exists_SpecMap_comp_eq_of_isAlgClosed_of_isClosed_singleton

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

theorem AlgebraicGeometry.Scheme.exists_SpecMap_comp_eq_of_isAlgClosed_of_isClosed_singleton
    {k₀ : Type u} [Field k₀] {F : Scheme.{u}} (f : F ⟶ Spec (CommRingCat.of k₀)) [LocallyOfFiniteType f]
    (k : Type u) [Field k] [Algebra k₀ k] [IsAlgClosed k]
    (y : F) (hy : IsClosed ({y} : Set F)) :
    ∃ z : Spec (CommRingCat.of k) ⟶ F,
      z ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k₀ k)) ∧ z.base (IsLocalRing.closedPoint k) = y := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_SpecMap_comp_eq_of_isAlgClosed_of_isClosed_singleton.solution

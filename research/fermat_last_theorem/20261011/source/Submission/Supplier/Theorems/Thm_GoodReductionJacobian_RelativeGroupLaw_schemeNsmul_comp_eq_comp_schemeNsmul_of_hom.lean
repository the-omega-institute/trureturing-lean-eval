import Mathlib
import Submission.Supplier.Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Submission.Supplier.Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_schemeNsmul_comp_eq_comp_schemeNsmul_of_hom

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
attribute [-simp] GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.schemeNsmul_comp_eq_comp_schemeNsmul_of_hom
    {R : Type u} [CommRing R]
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} (LB : RelativeGroupLaw R g)
    {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (u : SchemeHomOver g f)
    (hu : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g),
      NeronModelInfra.schemeHomOverComp (LB.mul t x y) u =
        L.mul t (NeronModelInfra.schemeHomOverComp x u) (NeronModelInfra.schemeHomOverComp y u)) :
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
        NeronModelInfra.schemeHomOverComp (LB.one t) u = L.one t) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t g),
        NeronModelInfra.schemeHomOverComp (LB.nsmul t n x) u =
          L.nsmul t n (NeronModelInfra.schemeHomOverComp x u)) ∧
    (∀ n : ℕ, LB.schemeNsmul n ≫ u.1 = u.1 ≫ L.schemeNsmul n) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_schemeNsmul_comp_eq_comp_schemeNsmul_of_hom.solution

import Mathlib
import Submission.Supplier.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_NeronModelInfra_neronUniqueExtension_of_forall_quasiCompact

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

theorem NeronModelInfra.neronUniqueExtension_of_forall_quasiCompact
    (R : Type u) [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsSeparated f]
    (h : ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of R)), Smooth t → QuasiCompact t →
      Function.Bijective (genericFibreRestrict R K f t)) :
    NeronUniqueExtension R K f := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_neronUniqueExtension_of_forall_quasiCompact.solution

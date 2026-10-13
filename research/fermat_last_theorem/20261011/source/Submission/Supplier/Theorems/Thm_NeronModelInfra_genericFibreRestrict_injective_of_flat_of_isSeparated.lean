import Mathlib
import Submission.Supplier.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_NeronModelInfra_genericFibreRestrict_injective_of_flat_of_isSeparated

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

theorem NeronModelInfra.genericFibreRestrict_injective_of_flat_of_isSeparated
    (R : Type u) [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X T : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (t : T ⟶ Spec (CommRingCat.of R))
    [IsSeparated f] [Flat t] :
    Function.Injective (genericFibreRestrict R K f t) := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_genericFibreRestrict_injective_of_flat_of_isSeparated.solution

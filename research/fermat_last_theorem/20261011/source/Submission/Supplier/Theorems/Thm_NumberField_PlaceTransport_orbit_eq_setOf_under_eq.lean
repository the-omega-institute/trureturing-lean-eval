import Mathlib
import Submission.Supplier.Definitions.Def_NumberField_PlaceTransport
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_NumberField_PlaceTransport_orbit_eq_setOf_under_eq

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false
open scoped NumberField.PlaceTransport
theorem NumberField.PlaceTransport.orbit_eq_setOf_under_eq (E K : Type*) [Field E] [Field K] [NumberField K]
    [Algebra E K] [IsGalois E K] (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    MulAction.orbit (K ≃ₐ[E] K) w =
      {w' | w'.under (NumberField.RingOfIntegers E) = w.under (NumberField.RingOfIntegers E)} := by p2m_exact_reverting @_root_.P2MW.S_NumberField_PlaceTransport_orbit_eq_setOf_under_eq.solution

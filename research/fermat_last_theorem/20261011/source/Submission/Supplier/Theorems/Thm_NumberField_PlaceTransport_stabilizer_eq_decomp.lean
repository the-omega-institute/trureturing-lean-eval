import Mathlib
import Submission.Supplier.Definitions.Def_NumberField_PlaceTransport
import Submission.Supplier.Definitions.Def_NumberField_PlaceDecompositionAction
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_NumberField_PlaceTransport_stabilizer_eq_decomp

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false
open scoped NumberField.PlaceTransport
theorem NumberField.PlaceTransport.stabilizer_eq_decomp (E K : Type*) [Field E] [Field K] [NumberField K] [Algebra E K]
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    MulAction.stabilizer (K ≃ₐ[E] K) w = NumberField.PlaceDecomp.decomp E K w := by p2m_exact_reverting @_root_.P2MW.S_NumberField_PlaceTransport_stabilizer_eq_decomp.solution

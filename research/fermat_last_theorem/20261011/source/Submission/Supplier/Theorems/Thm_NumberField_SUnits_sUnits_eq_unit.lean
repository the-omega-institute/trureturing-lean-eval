import Mathlib
import Submission.Supplier.Definitions.Def_NumberField_PlaceAbove
import Submission.Supplier.Definitions.Def_NumberField_PlaceDecompositionAction
import Submission.Supplier.Definitions.Def_NumberField_SUnitsModule
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_NumberField_SUnits_sUnits_eq_unit

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false
theorem NumberField.SUnits.sUnits_eq_unit (E K : Type) [Field E] [Field K] [NumberField K] [Algebra E K]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))) :
    NumberField.SUnits.sUnits E K S = Set.unit (NumberField.SUnits.placesAbove E K S) K := by p2m_exact_reverting @_root_.P2MW.S_NumberField_SUnits_sUnits_eq_unit.solution

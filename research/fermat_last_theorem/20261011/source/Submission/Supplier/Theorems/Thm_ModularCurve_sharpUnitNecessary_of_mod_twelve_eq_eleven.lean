import Submission.Supplier.Definitions.Def_ModularCurve_EtaQuotient
import Submission.Supplier.Definitions.Def_NumberTheory_DedekindSum
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_ModularCurve_sharpUnitNecessary_of_mod_twelve_eq_eleven

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

theorem ModularCurve.sharpUnitNecessary_of_mod_twelve_eq_eleven (j : ℕ) : ModularCurve.SharpUnitNecessary (12 * j + 11) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_sharpUnitNecessary_of_mod_twelve_eq_eleven.solution

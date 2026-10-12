import Mathlib
import Submission.Supplier.Definitions.Def_ModularCurve_X1Diamond
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_ModularCurve_diamondOneBar_comm

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

theorem ModularCurve.diamondOneBar_comm (M d e : ℕ) :
    ModularCurve.diamondOneBar M d * ModularCurve.diamondOneBar M e =
      ModularCurve.diamondOneBar M e * ModularCurve.diamondOneBar M d := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_diamondOneBar_comm.solution

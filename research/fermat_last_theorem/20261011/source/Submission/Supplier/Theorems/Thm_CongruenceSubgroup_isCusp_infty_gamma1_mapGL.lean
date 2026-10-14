import Mathlib
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_CongruenceSubgroup_isCusp_infty_gamma1_mapGL

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

theorem CongruenceSubgroup.isCusp_infty_gamma1_mapGL (M : ℕ) :
    IsCusp OnePoint.infty (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ)
      (CongruenceSubgroup.Gamma1 M)) := by p2m_exact_reverting @_root_.P2MW.S_CongruenceSubgroup_isCusp_infty_gamma1_mapGL.solution

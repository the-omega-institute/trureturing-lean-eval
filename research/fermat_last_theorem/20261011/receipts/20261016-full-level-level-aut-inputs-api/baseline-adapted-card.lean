import Submission.Supplier.Definitions.Def_ModularCurve_FullLevelJacobian
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_ModularCurve_FullLevel_levelAutInputs_of_not_dvd

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel

theorem ModularCurve.FullLevel.levelAutInputs_of_not_dvd (q : ℕ) [Fact q.Prime] (M' : ℕ)
    (hqM' : ¬ q ∣ M') : ModularCurve.FullLevel.LevelAutInputs q M' := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_levelAutInputs_of_not_dvd.solution

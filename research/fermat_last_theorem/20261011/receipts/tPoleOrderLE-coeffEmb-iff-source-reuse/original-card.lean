import Submission.Supplier.Definitions.Def_ModularCurve_X0
import Submission.Supplier.Definitions.Def_ModularCurve_PhiGen
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_ModularCurve_PhiGen_tPoleOrderLE_coeffEmb_iff

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.PhiGen.tPoleOrderLE_coeffEmb_iff {K : Type*} [Field K] [Algebra ℚ K] (f : LaurentSeries ℚ) (n : ℕ) : TPoleOrderLE (coeffEmb K f) n ↔ TPoleOrderLE f n := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PhiGen_tPoleOrderLE_coeffEmb_iff.solution

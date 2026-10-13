import Submission.Supplier.Definitions.Def_ModularCurve_X0
import Submission.Supplier.Definitions.Def_ModularCurve_PhiGen
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_ModularCurve_minpoly_jqN_eq_toAdjoin

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.minpoly_jqN_eq_toAdjoin {N : ℕ} [NeZero N] (data : ModularPolynomialData N) (h : PhiIrreducible data) : minpoly (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (jqN N) = data.toAdjoin := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_minpoly_jqN_eq_toAdjoin.solution

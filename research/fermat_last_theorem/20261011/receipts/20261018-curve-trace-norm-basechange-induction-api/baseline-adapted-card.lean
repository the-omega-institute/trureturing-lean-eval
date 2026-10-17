import Submission.Supplier.Definitions.Def_ModularCurve_QExpansionDiff
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_AlgebraicCurve_traceDiff_inv_smul_D_eq_inv_norm_smul_D_norm

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

theorem AlgebraicCurve.traceDiff_inv_smul_D_eq_inv_norm_smul_D_norm (K F F' : Type*) [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsSeparable F F'] (h : F') : traceDiff K F F' (h⁻¹ • KaehlerDifferential.D K F' h) = (Algebra.norm F h)⁻¹ • KaehlerDifferential.D K F (Algebra.norm F h) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_traceDiff_inv_smul_D_eq_inv_norm_smul_D_norm.solution

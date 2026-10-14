import Submission.Supplier.Definitions.Def_AlgebraicCurve_Correspondence
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_AlgebraicCurve_finrankAlong_comp

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

theorem AlgebraicCurve.finrankAlong_comp {K F F' F'' : Type*} [Field K] [Field F] [Field F'] [Field F''] [Algebra K F] [Algebra K F'] [Algebra K F''] (φ : F →ₐ[K] F') (χ : F' →ₐ[K] F'') : AlgebraicCurve.finrankAlong K (χ.comp φ) = AlgebraicCurve.finrankAlong K φ * AlgebraicCurve.finrankAlong K χ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_finrankAlong_comp.solution

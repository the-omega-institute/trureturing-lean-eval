import Submission.Supplier.Definitions.Def_AlgebraicCurve_Differentials
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_AlgebraicCurve_pullbackDiff_smul

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

open AlgebraicCurve
theorem AlgebraicCurve.pullbackDiff_smul {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] (φ : F →ₐ[K] F') (g : F) (ω : Ω[F⁄K]) :
    pullbackDiff φ (g • ω) = φ g • pullbackDiff φ ω := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_pullbackDiff_smul.solution

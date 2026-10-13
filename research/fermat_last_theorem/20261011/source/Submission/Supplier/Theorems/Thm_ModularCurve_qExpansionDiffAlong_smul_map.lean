import Submission.Supplier.Definitions.Def_ModularCurve_QExpansionDiff
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_ModularCurve_qExpansionDiffAlong_smul_map

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

theorem ModularCurve.qExpansionDiffAlong_smul_map {K F F' L : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Field L] [Algebra K L] (σ : F' →ₐ[K] LaurentSeries L) (h : F') (ω : Ω[F⁄K]) : qExpansionDiffAlong σ (h • KaehlerDifferential.map K K F F' ω) = σ h * qExpansionDiffAlong (σ.comp (IsScalarTower.toAlgHom K F F')) ω := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_qExpansionDiffAlong_smul_map.solution

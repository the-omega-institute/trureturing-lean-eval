import Submission.Supplier.Definitions.Def_ModularCurve_EtaQuotient
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_ModularCurve_hasSum_smul_sharpUnitSeries_qParam

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
attribute [-simp] ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single

theorem ModularCurve.hasSum_smul_sharpUnitSeries_qParam (ℓ : ℕ) [NeZero ℓ] (τ : UpperHalfPlane) : HasSum (fun m : ℤ => (((((ℓ : ℚ) ^ (ModularCurve.sharpExp ℓ / 2))⁻¹ • ModularCurve.sharpUnitSeries ℓ).coeff m : ℚ) : ℂ) * Function.Periodic.qParam ℓ (τ : ℂ) ^ m) ((ModularCurve.sharpUnitFun ℓ (ModularGroup.S • τ))⁻¹) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_hasSum_smul_sharpUnitSeries_qParam.solution

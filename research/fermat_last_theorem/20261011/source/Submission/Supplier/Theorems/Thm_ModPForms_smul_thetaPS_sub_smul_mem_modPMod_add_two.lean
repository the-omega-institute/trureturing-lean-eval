import Submission.Supplier.Definitions.Def_CuspForm_ModPForms
import Submission.Supplier.Definitions.Def_SwdAlgebra
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_ModPForms_smul_thetaPS_sub_smul_mem_modPMod_add_two

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
set_option autoImplicit false

theorem ModPForms.smul_thetaPS_sub_smul_mem_modPMod_add_two (N' : ℕ) [NeZero N'] (F : Type) [Field F] (k : ℤ)
    (φ : PowerSeries F) (hφ : φ ∈ ModPForms.modPMod N' k F) :
    (12 : F) • ModPForms.thetaPS φ - (k : F) • (SwdAlgebra.qP F * φ) ∈ ModPForms.modPMod N' (k + 2) F := by p2m_exact_reverting @_root_.P2MW.S_ModPForms_smul_thetaPS_sub_smul_mem_modPMod_add_two.solution

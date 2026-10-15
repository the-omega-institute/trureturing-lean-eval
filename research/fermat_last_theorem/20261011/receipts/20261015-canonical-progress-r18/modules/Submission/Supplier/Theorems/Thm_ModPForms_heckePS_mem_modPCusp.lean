import Submission.Supplier.Definitions.Def_CuspForm_ModPForms
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_ModPForms_heckePS_mem_modPCusp

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
attribute [-simp] ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL
set_option autoImplicit false

theorem ModPForms.heckePS_mem_modPCusp (N' : ℕ) [NeZero N'] (F : Type) [Field F]
    (k : ℤ) (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N')
    (φ : PowerSeries F) (hφ : φ ∈ ModPForms.modPCusp N' k F) :
    ModPForms.heckePS k ℓ φ ∈ ModPForms.modPCusp N' k F := by p2m_exact_reverting @_root_.P2MW.S_ModPForms_heckePS_mem_modPCusp.solution

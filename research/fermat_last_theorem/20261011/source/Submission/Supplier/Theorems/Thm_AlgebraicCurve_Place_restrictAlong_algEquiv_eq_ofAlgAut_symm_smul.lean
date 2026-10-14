import Mathlib
import Submission.Supplier.Definitions.Def_AlgebraicCurve_Correspondence
import Submission.Supplier.Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_AlgebraicCurve_Place_restrictAlong_algEquiv_eq_ofAlgAut_symm_smul

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Place.restrictAlong_algEquiv_eq_ofAlgAut_symm_smul
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (σ : F ≃ₐ[K] F) (hσ : σ.toAlgHom.toRingHom.IsIntegral) (v : Place K F) :
    v.restrictAlong σ.toAlgHom hσ = SemilinearAut.ofAlgAut σ.symm • v := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_restrictAlong_algEquiv_eq_ofAlgAut_symm_smul.solution

import Submission.Supplier.Definitions.Def_ModularCurve_FullLevelJacobian
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_ModularCurve_FullLevel_tateGal_mul_tateGL2_comm

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

theorem ModularCurve.FullLevel.tateGal_mul_tateGL2_comm
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') (lam : ℕ) [Fact lam.Prime] :
    ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : CuspidalType.GL2 q),
      ModularCurve.FullLevel.tateGal q M' lam σ * ModularCurve.FullLevel.tateGL2 q M' lam x =
        ModularCurve.FullLevel.tateGL2 q M' lam x * ModularCurve.FullLevel.tateGal q M' lam σ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_tateGal_mul_tateGL2_comm.solution

#print axioms ModularCurve.FullLevel.tateGal_mul_tateGL2_comm

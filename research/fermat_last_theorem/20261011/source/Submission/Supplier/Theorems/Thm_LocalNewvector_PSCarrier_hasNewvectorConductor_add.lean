import Submission.Supplier.Definitions.Def_LocalNewvector_CharConductor
import Submission.Supplier.Definitions.Def_LocalNewvector_PrincipalSeriesCarrier
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
attribute [-instance] FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete FLT.SpectralSide.instCompactSpaceMatrix
attribute [-simp] FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv

theorem LocalNewvector.PSCarrier.hasNewvectorConductor_add (p : ℕ) [Fact p.Prime] {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ}
    {n₁ n₂ : ℕ} (h₁ : LocalNewvector.HasCharConductor p μ₁ n₁) (h₂ : LocalNewvector.HasCharConductor p μ₂ n₂) :
    LocalNewvector.HasNewvectorConductor p (LocalNewvector.PSCarrier p μ₁ μ₂) (n₁ + n₂) := by p2m_exact_reverting @_root_.P2MW.S_LocalNewvector_PSCarrier_hasNewvectorConductor_add.solution

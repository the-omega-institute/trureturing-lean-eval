import Mathlib
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_WeierstrassCurve_nonempty_functionField_algEquiv_of_variableChange

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
attribute [-instance] WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_submission WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_submission WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_submission
attribute [-simp] WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero

universe u
theorem WeierstrassCurve.nonempty_functionField_algEquiv_of_variableChange
    {F : Type u} [Field F] (W : WeierstrassCurve F) (C : WeierstrassCurve.VariableChange F) :
    Nonempty (W.toAffine.FunctionField ≃ₐ[F] (C • W).toAffine.FunctionField) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_nonempty_functionField_algEquiv_of_variableChange.solution

#print axioms WeierstrassCurve.nonempty_functionField_algEquiv_of_variableChange

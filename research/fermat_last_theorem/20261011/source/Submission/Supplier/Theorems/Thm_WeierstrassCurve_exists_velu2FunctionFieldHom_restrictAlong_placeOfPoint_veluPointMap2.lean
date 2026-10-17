import Mathlib
import Submission.Supplier.Definitions.Def_Isogeny_ConditionalCurrency
import Submission.Supplier.Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred
import Submission.Supplier.Definitions.Def_WeierstrassCurve_VeluPointMap2
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_WeierstrassCurve_exists_velu2FunctionFieldHom_restrictAlong_placeOfPoint_veluPointMap2

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
attribute [-instance] WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_submission WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_submission WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_submission WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral
attribute [-simp] WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal

set_option autoImplicit false

theorem WeierstrassCurve.exists_velu2FunctionFieldHom_restrictAlong_placeOfPoint_veluPointMap2
    {F : Type*} [Field F] [DecidableEq F] [CharZero F] [IsAlgClosed F]
    {W : WeierstrassCurve F} [W.IsElliptic]
    {x₀ y₀ : F} (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0)
    (hΔ' : (W.veluQuotient2 x₀ y₀).Δ ≠ 0)
    [(W.veluQuotient2 x₀ y₀).IsElliptic]
    [WeierstrassCurve.Affine.GenusOnePlaceGate W.toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W.toAffine]
    [WeierstrassCurve.Affine.AbelTheorem W.toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate (W.veluQuotient2 x₀ y₀).toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (W.veluQuotient2 x₀ y₀).toAffine]
    [WeierstrassCurve.Affine.AbelTheorem (W.veluQuotient2 x₀ y₀).toAffine] :
    ∃ (ι : (W.veluQuotient2 x₀ y₀).toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField)
      (hι : ι.toRingHom.IsIntegral) (_hfin : AlgebraicCurve.FiniteAlong F ι),
      ∀ P : W.toAffine.Point,
        (WeierstrassCurve.Affine.placeOfPoint P).restrictAlong ι hι
          = WeierstrassCurve.Affine.placeOfPoint
              (WeierstrassCurve.veluPointMap2 two_ne_zero hQ hgy hΔ' P) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_velu2FunctionFieldHom_restrictAlong_placeOfPoint_veluPointMap2.solution

#print axioms WeierstrassCurve.exists_velu2FunctionFieldHom_restrictAlong_placeOfPoint_veluPointMap2

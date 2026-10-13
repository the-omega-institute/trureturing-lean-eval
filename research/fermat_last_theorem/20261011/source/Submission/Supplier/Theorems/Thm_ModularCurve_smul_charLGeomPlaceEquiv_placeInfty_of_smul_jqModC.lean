import Submission.Supplier.Definitions.Def_ModularCurve_SpecializeModuli
import Submission.Supplier.Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Submission.Supplier.Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_ModularCurve_smul_charLGeomPlaceEquiv_placeInfty_of_smul_jqModC

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
attribute [-instance] AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one

open AlgebraicCurve AlgebraicCurve.RationalFunctionField ModularCurve
theorem ModularCurve.smul_charLGeomPlaceEquiv_placeInfty_of_smul_jqModC {K : Type*} [Field K]
    [DecidableEq (RatFunc K)] (g : SemilinearAut K (modularFunctionFieldC K 1))
    (hg : g • (⟨jqModC K, jqModC_mem K 1⟩ : modularFunctionFieldC K 1)
      = ⟨jqModC K, jqModC_mem K 1⟩) :
    g • charLGeomPlaceEquiv K (placeInfty K) = charLGeomPlaceEquiv K (placeInfty K) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_smul_charLGeomPlaceEquiv_placeInfty_of_smul_jqModC.solution

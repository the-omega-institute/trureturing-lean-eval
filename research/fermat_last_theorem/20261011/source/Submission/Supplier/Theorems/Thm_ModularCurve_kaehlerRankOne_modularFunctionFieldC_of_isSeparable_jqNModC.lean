import Submission.Supplier.Definitions.Def_AlgebraicCurve_IsCurveOver
import Submission.Supplier.Definitions.Def_ModularCurve_JqCoeff
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_ModularCurve_kaehlerRankOne_modularFunctionFieldC_of_isSeparable_jqNModC

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
open AlgebraicCurve ModularCurve KaehlerDifferential
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
theorem ModularCurve.kaehlerRankOne_modularFunctionFieldC_of_isSeparable_jqNModC
    (K : Type*) [Field K] (N : ℕ) [NeZero N]
    (hsep : IsSeparable (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
      (jqNModC K N)) :
    Module.Free (modularFunctionFieldC K N) Ω[(modularFunctionFieldC K N)⁄K]
      ∧ Module.finrank (modularFunctionFieldC K N) Ω[(modularFunctionFieldC K N)⁄K] = 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_kaehlerRankOne_modularFunctionFieldC_of_isSeparable_jqNModC.solution

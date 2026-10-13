import Submission.Supplier.Definitions.Def_ModularCurve_JqCoeff
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_ModularCurve_modularFunctionFieldC_mul_eq_of_isSeparable

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

open ModularCurve
theorem ModularCurve.modularFunctionFieldC_mul_eq_of_isSeparable (K : Type*) [Field K] (N : ℕ) [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hsep : IsSeparable (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) (jqNModC K N)) :
    modularFunctionFieldC K (N * ℓ) = modularFunctionFieldC K N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_modularFunctionFieldC_mul_eq_of_isSeparable.solution

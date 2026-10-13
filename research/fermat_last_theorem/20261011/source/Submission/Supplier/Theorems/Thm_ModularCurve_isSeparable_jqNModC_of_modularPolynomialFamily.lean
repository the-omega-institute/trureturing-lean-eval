import Submission.Supplier.Definitions.Def_ModularCurve_JqCoeff
import Submission.Supplier.Definitions.Def_ModularCurve_PhiGen
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_ModularCurve_isSeparable_jqNModC_of_modularPolynomialFamily

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

open ModularCurve
theorem ModularCurve.isSeparable_jqNModC_of_modularPolynomialFamily (K : Type*) [Field K] (hΦ : ModularPolynomialFamily) (N : ℕ) [Fact N.Prime]
    (hNK : (N : K) ≠ 0) :
    IsSeparable (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) (jqNModC K N) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_isSeparable_jqNModC_of_modularPolynomialFamily.solution

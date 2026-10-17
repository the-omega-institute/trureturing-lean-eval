import Mathlib
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_ValuationSubring_isPrincipalIdealRing_of_finiteDimensional_adjoin

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

theorem ValuationSubring.isPrincipalIdealRing_of_finiteDimensional_adjoin
    {K F : Type*} [Field K] [Field F] [Algebra K F] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (O : ValuationSubring F) (hK : ∀ a : K, algebraMap K F a ∈ O) (hO : O ≠ ⊤) :
    IsPrincipalIdealRing O := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_isPrincipalIdealRing_of_finiteDimensional_adjoin.solution

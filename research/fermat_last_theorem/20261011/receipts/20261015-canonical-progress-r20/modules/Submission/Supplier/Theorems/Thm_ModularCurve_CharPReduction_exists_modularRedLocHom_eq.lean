import Submission.Supplier.Definitions.Def_ModularCurve_CharPReduction
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_ModularCurve_CharPReduction_exists_modularRedLocHom_eq

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

open ModularCurve CharPReduction
theorem ModularCurve.CharPReduction.exists_modularRedLocHom_eq {L : Type*} [Field L] (A : Subring L)
    {k : Type*} [Field k] (red : A →+* k) (N : ℕ) [NeZero N]
    (hred : Function.Surjective red)
    {y : LaurentSeries k} (hy : y ∈ modularFunctionFieldC k N) :
    ∃ f : modularLocalized N A red, modularRedLocHom N A red f = y := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_CharPReduction_exists_modularRedLocHom_eq.solution

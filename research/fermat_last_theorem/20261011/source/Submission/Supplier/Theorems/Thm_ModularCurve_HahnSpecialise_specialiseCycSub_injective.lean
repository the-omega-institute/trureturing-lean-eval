import Submission.Supplier.Definitions.Def_ModularCurve_HahnSpecialise
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_ModularCurve_HahnSpecialise_specialiseCycSub_injective

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

open ModularCurve ModularCurve.B3 ModularCurve.HahnSpecialise
open ModularCurve.TatePoint (Qbar H CycSubH)
open scoped Classical

theorem ModularCurve.HahnSpecialise.specialiseCycSub_injective (E : WeierstrassCurve H) (hE : IntegralCoeffs E)
    (hΔ : (specialFibre E).Δ ≠ 0) (N : ℕ) [NeZero N] :
    Function.Injective (specialiseCycSub E hE hΔ N) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_HahnSpecialise_specialiseCycSub_injective.solution

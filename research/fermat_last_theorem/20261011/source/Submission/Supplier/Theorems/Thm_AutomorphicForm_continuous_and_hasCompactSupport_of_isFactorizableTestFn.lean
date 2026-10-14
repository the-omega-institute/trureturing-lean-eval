import Submission.Supplier.Definitions.Def_AutomorphicForm_FactorizableTestFn
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

open NumberField IsDedekindDomain
theorem AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn (F : Type) [Field F] [NumberField F]
    (f : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ) (hf : AutomorphicForm.IsFactorizableTestFn F f) :
    Continuous f ∧ HasCompactSupport f := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn.solution

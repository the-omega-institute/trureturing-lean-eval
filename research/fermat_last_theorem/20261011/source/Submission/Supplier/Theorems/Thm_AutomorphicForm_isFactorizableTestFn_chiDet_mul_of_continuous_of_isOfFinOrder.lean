import Mathlib
import Submission.Supplier.Definitions.Def_AutomorphicForm_FactorizableTestFn
import Submission.Supplier.Definitions.Def_AutomorphicForm_AdelicLsXi
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_AutomorphicForm_isFactorizableTestFn_chiDet_mul_of_continuous_of_isOfFinOrder

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open NumberField IsDedekindDomain
open AutomorphicForm

theorem AutomorphicForm.isFactorizableTestFn_chiDet_mul_of_continuous_of_isOfFinOrder
    (F : Type) [Field F] [NumberField F]
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hηc : Continuous η) (hηo : IsOfFinOrder η)
    (f : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ) (hf : IsFactorizableTestFn F f) :
    IsFactorizableTestFn F (fun g => chiDet (𝓞 F) F η g * f g) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isFactorizableTestFn_chiDet_mul_of_continuous_of_isOfFinOrder.solution

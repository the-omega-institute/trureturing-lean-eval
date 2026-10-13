import Mathlib
import Submission.Supplier.Definitions.Def_QuaternionAlgebra_Order
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_QuaternionAlgebra_IsOrder_finrank_eq_four

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

open scoped Quaternion

theorem QuaternionAlgebra.IsOrder.finrank_eq_four {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (hΛ : QuaternionAlgebra.IsOrder Λ) : Module.finrank ℤ Λ = 4 := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsOrder_finrank_eq_four.solution

import Mathlib
import Submission.Supplier.Definitions.Def_QuaternionAlgebra_Order
import Submission.Supplier.Definitions.Def_QuaternionAlgebra_ReducedNorm
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open scoped Quaternion

theorem QuaternionAlgebra.IsOrder.exists_intCast_eq_nrd_and_exists_intCast_eq_trd
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    {x : ℍ[ℚ, a, b]} (hx : x ∈ Λ) :
    (∃ n : ℤ, (n : ℚ) = QuaternionAlgebra.nrd x) ∧ ∃ t : ℤ, (t : ℚ) = QuaternionAlgebra.trd x := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd.solution

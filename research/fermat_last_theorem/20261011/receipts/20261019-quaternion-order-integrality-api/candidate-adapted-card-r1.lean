import Mathlib
import Submission.Supplier.Definitions.Def_QuaternionAlgebra_Order
import Submission.Supplier.Definitions.Def_QuaternionAlgebra_ReducedNorm
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_QuaternionAlgebra_IsOrder_exists_int_trd_eq_and_nrd_eq

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

open scoped Quaternion
theorem QuaternionAlgebra.IsOrder.exists_int_trd_eq_and_nrd_eq
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    {x : ℍ[ℚ, a, b]} (hx : x ∈ Λ) :
    (∃ t n : ℤ, QuaternionAlgebra.trd x = t ∧ QuaternionAlgebra.nrd x = n) ∧
      (∀ r : ℚ, r • (1 : ℍ[ℚ, a, b]) ∈ Λ → ∃ k : ℤ, (k : ℚ) = r) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsOrder_exists_int_trd_eq_and_nrd_eq.solution

#print axioms QuaternionAlgebra.IsOrder.exists_int_trd_eq_and_nrd_eq

import Mathlib
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_Complex_tsum_int_one_div_add_sq_eq_pi_sq_div_sin_sq

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open scoped MatrixGroups ModularForm Topology Real Matrix

theorem Complex.tsum_int_one_div_add_sq_eq_pi_sq_div_sin_sq (z : ℂ) (hz : z ∈ Complex.integerComplement) :
    ∑' n : ℤ, 1 / (z + n) ^ 2 = (π : ℂ) ^ 2 / Complex.sin (π * z) ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_Complex_tsum_int_one_div_add_sq_eq_pi_sq_div_sin_sq.solution

#print axioms Complex.tsum_int_one_div_add_sq_eq_pi_sq_div_sin_sq

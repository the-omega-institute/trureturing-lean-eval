import Mathlib
import Submission.Supplier.Definitions.Def_ModularCurve_SupersingularModuli
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_ModularCurve_eq_zero_of_mem_ssJSet_three

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open ModularCurve
theorem ModularCurve.eq_zero_of_mem_ssJSet_three
    {k : Type*} [Field k] [CharP k 3] [DecidableEq k]
    (a : k) (ha : a ∈ ssJSet 3 k) (ha2 : a ^ (3 ^ 2) = a) : a = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_eq_zero_of_mem_ssJSet_three.solution

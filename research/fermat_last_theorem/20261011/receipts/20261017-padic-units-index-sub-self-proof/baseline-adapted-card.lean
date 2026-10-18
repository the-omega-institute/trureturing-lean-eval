import Mathlib
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_Padic_index_range_powMonoidHom_units_of_ne_two

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

theorem Padic.index_range_powMonoidHom_units_of_ne_two {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    ((powMonoidHom p : (ℚ_[p])ˣ →* (ℚ_[p])ˣ).range).index = p ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_Padic_index_range_powMonoidHom_units_of_ne_two.solution

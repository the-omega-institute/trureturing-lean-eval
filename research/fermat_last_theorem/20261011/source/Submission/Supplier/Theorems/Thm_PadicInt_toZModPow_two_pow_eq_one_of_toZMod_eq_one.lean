import Mathlib
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_PadicInt_toZModPow_two_pow_eq_one_of_toZMod_eq_one

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

theorem PadicInt.toZModPow_two_pow_eq_one_of_toZMod_eq_one {p : ℕ} [hp : Fact p.Prime]
    {z : ℤ_[p]} (hz : PadicInt.toZMod z = 1) :
    PadicInt.toZModPow 2 (z ^ p) = 1 := by p2m_exact_reverting @_root_.P2MW.S_PadicInt_toZModPow_two_pow_eq_one_of_toZMod_eq_one.solution

#print axioms PadicInt.toZModPow_two_pow_eq_one_of_toZMod_eq_one

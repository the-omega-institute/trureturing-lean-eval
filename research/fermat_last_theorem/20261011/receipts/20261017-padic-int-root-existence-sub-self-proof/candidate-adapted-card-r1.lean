import Mathlib
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_PadicInt_exists_pow_eq_of_toZModPow_two_eq_one

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

theorem PadicInt.exists_pow_eq_of_toZModPow_two_eq_one {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {u : ℤ_[p]} (hu : PadicInt.toZModPow 2 u = 1) :
    ∃ z : ℤ_[p], PadicInt.toZMod z = 1 ∧ z ^ p = u := by p2m_exact_reverting @_root_.P2MW.S_PadicInt_exists_pow_eq_of_toZModPow_two_eq_one.solution

#print axioms PadicInt.exists_pow_eq_of_toZModPow_two_eq_one

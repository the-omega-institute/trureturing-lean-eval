import Mathlib
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_PadicInt_dvd_of_one_add_prime_pow_eq_pow

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

theorem PadicInt.dvd_of_one_add_prime_pow_eq_pow {p : ℕ} [hp : Fact p.Prime]
    {j : ℕ} {z : ℤ_[p]} (h : (1 + p : ℤ_[p]) ^ j = z ^ p) : p ∣ j := by p2m_exact_reverting @_root_.P2MW.S_PadicInt_dvd_of_one_add_prime_pow_eq_pow.solution

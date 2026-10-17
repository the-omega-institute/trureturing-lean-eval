import Mathlib
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_Padic_dvd_of_prime_zpow_mul_one_add_prime_zpow_eq_pow

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

theorem Padic.dvd_of_prime_zpow_mul_one_add_prime_zpow_eq_pow {p : ℕ} [hp : Fact p.Prime]
    {i j : ℤ} {y : ℚ_[p]}
    (h : (p : ℚ_[p]) ^ i * (1 + p : ℚ_[p]) ^ j = y ^ p) :
    (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j := by p2m_exact_reverting @_root_.P2MW.S_Padic_dvd_of_prime_zpow_mul_one_add_prime_zpow_eq_pow.solution

#print axioms Padic.dvd_of_prime_zpow_mul_one_add_prime_zpow_eq_pow

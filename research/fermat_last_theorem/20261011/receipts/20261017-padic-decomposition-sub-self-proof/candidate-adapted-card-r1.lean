import Mathlib
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_Padic_exists_eq_prime_pow_mul_one_add_prime_pow_mul_pow

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

theorem Padic.exists_eq_prime_pow_mul_one_add_prime_pow_mul_pow {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) {x : ℚ_[p]} (hx : x ≠ 0) :
    ∃ i < p, ∃ j < p, ∃ y : ℚ_[p], y ≠ 0 ∧
      x = (p : ℚ_[p]) ^ i * (1 + p : ℚ_[p]) ^ j * y ^ p := by p2m_exact_reverting @_root_.P2MW.S_Padic_exists_eq_prime_pow_mul_one_add_prime_pow_mul_pow.solution

#print axioms Padic.exists_eq_prime_pow_mul_one_add_prime_pow_mul_pow

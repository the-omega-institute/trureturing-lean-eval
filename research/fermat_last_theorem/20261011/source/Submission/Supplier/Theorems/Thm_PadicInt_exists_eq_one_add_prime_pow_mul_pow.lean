import Mathlib
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_PadicInt_exists_eq_one_add_prime_pow_mul_pow

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

theorem PadicInt.exists_eq_one_add_prime_pow_mul_pow {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {u : ℤ_[p]} (hu : ‖u‖ = 1) :
    ∃ j < p, ∃ z : ℤ_[p], u = (1 + p : ℤ_[p]) ^ j * z ^ p := by p2m_exact_reverting @_root_.P2MW.S_PadicInt_exists_eq_one_add_prime_pow_mul_pow.solution

#print axioms PadicInt.exists_eq_one_add_prime_pow_mul_pow

import Mathlib
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_Polynomial_X_pow_sub_C_irreducible_of_isCoprime_apply

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

open Polynomial

theorem Polynomial.X_pow_sub_C_irreducible_of_isCoprime_apply
    {F : Type*} [Field F] (v : F → ℤ) (hv : ∀ x y : F, x ≠ 0 → y ≠ 0 → v (x * y) = v x + v y)
    {n : ℕ} (hn : 0 < n) {a : F} (ha : a ≠ 0) (hcop : IsCoprime (v a) n) :
    Irreducible (X ^ n - C a) := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_X_pow_sub_C_irreducible_of_isCoprime_apply.solution

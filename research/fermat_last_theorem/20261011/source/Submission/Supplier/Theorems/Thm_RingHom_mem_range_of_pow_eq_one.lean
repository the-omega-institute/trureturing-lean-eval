import Mathlib
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_RingHom_mem_range_of_pow_eq_one

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

theorem RingHom.mem_range_of_pow_eq_one {F : Type*} [Field F] [IsAlgClosed F] [CharZero F]
    (σ : F →+* ℂ) {ζ : ℂ} {n : ℕ} (hn : 0 < n) (hζ : ζ ^ n = 1) : ζ ∈ σ.range := by p2m_exact_reverting @_root_.P2MW.S_RingHom_mem_range_of_pow_eq_one.solution

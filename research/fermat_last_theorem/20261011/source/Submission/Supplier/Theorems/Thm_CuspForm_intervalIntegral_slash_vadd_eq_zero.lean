import Mathlib
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_CuspForm_intervalIntegral_slash_vadd_eq_zero

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem CuspForm.intervalIntegral_slash_vadd_eq_zero
    {M : ℕ} [NeZero M] {k : ℤ} (h : CuspForm (CongruenceSubgroup.Gamma1 M) k) (ρ : SL(2, ℤ))
    (z : UpperHalfPlane) :
    ∫ s in (0 : ℝ)..(M : ℝ), ((⇑h) ∣[k] (ρ : GL (Fin 2) ℝ)) (s +ᵥ z) = 0 := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_intervalIntegral_slash_vadd_eq_zero.solution

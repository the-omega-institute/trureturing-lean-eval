import Submission.Supplier.Definitions.Def_ModularCurve_GenusNumerics
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_ModularCurve_cuspCount_mul_of_coprime

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

open ModularCurve
theorem ModularCurve.cuspCount_mul_of_coprime {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) (hMN : Nat.Coprime M N) : cuspCount (M * N) = cuspCount M * cuspCount N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_cuspCount_mul_of_coprime.solution

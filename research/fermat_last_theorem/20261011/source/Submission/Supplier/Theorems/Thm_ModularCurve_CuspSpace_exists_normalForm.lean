import Mathlib
import Submission.Supplier.Definitions.Def_ModularCurve_CuspSpace
import Submission.Supplier.Definitions.Def_ModularCurve_GenusNumerics
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_ModularCurve_CuspSpace_exists_normalForm

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

open OnePoint
theorem ModularCurve.CuspSpace.exists_normalForm {N : ℕ} (hN : N ≠ 0) (x : ModularCurve.CuspSpace N) :
    ∃ a : ℤ, IsCoprime a (ModularCurve.CuspSpace.cuspDenom N x : ℤ) ∧
      x = ModularCurve.CuspSpace.mk N (ModularCurve.ratPoint a (ModularCurve.CuspSpace.cuspDenom N x)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_CuspSpace_exists_normalForm.solution

import Submission.Supplier.Definitions.Def_ModularCurve_ModularUnit
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_ModularCurve_eisensteinNumerator_eq_gcd

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

open ModularCurve

theorem ModularCurve.eisensteinNumerator_eq_gcd (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) : eisensteinNumerator p = Nat.gcd ((p - 1) / 2) ((p ^ 2 - 1) / 24) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_eisensteinNumerator_eq_gcd.solution

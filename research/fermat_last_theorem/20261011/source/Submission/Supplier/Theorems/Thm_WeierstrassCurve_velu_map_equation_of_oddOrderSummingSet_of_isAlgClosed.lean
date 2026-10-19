import Mathlib
import Submission.Supplier.Definitions.Def_WeierstrassCurve_VeluPointMap
import Submission.Supplier.Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

open WeierstrassCurve
theorem WeierstrassCurve.velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed
    {L : Type*} [Field L] [DecidableEq L] [IsAlgClosed L]
    (W : WeierstrassCurve L) [W.IsElliptic] (n : ℕ) (Q : W.toAffine.Point)
    (hQ : addOrderOf Q = 2 * n + 1) {x y : L} (hxy : W.toAffine.Equation x y)
    (hx : ∀ A ∈ W.oddOrderSummingSet Q n, x ≠ A.1) :
    (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine.Equation
      (W.veluX (W.oddOrderSummingSet Q n) x) (W.veluY (W.oddOrderSummingSet Q n) x y) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed.solution

#print axioms WeierstrassCurve.velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed

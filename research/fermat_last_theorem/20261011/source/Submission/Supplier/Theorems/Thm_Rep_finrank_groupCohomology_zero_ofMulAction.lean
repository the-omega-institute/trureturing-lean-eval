import Mathlib
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_Rep_finrank_groupCohomology_zero_ofMulAction
import Submission.Supplier.Definitions.Def_Compat_Mathlib430

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false
theorem Rep.finrank_groupCohomology_zero_ofMulAction {G : Type} [Group G]
    (X : Type) [MulAction G X] [Finite X] :
    Module.finrank ℤ (groupCohomology (Rep.ofMulActionFinsupp ℤ G X) 0) = Nat.card (MulAction.orbitRel.Quotient G X) := by p2m_exact_reverting @_root_.P2MW.S_Rep_finrank_groupCohomology_zero_ofMulAction.solution

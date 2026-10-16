import Mathlib
import Submission.Supplier.Definitions.Def_GroupCohomology_ContinuousUnramified
import Submission.Supplier.Definitions.Def_DualSelmer_ExtConditions
import Submission.Supplier.Definitions.Def_ExtCitation_KummerBridge
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_Rep_finrank_invariants_res_dualTwist_eq

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation
theorem Rep.finrank_invariants_res_dualTwist_eq
    {p : ℕ} [Fact p.Prime] {H : Type} [Group H]
    (r : H →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional (ZMod p) M] :
    finrank (ZMod p) ((Rep.invariantsFunctor (ZMod p) H).obj (Rep.res r (M.dualTwist (cycloChar p))))
      = finrank (ZMod p) ((Rep.invariantsFunctor (ZMod p) H).obj ((Rep.res r M).dualTwist ((cycloChar p).comp r))) := by p2m_exact_reverting @_root_.P2MW.S_Rep_finrank_invariants_res_dualTwist_eq.solution

#print axioms Rep.finrank_invariants_res_dualTwist_eq

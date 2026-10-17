import Mathlib
import Submission.Supplier.Definitions.Def_ExtEndgame_ProductionDatum
import Submission.Supplier.Definitions.Def_GroupCohomology_ContinuousH2
import Submission.Supplier.Definitions.Def_DualSelmer_ExtConditions
import Submission.Supplier.Definitions.Def_ExtCitation_KummerBridge
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_groupCohomology_exists_injective_dual_continuousH2_archimedean

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation
theorem groupCohomology.exists_injective_dual_continuousH2_archimedean
    (p : ℕ) [Fact p.Prime] (S : Finset Nat.Primes) :
    ∃ inv : continuousH2 (extArithLoc S (Sum.inl ()))
        (ofChar (k := ZMod p) ((cycloChar p).comp (extArithLoc S (Sum.inl ())))) →ₗ[ZMod p] ZMod p,
      Function.Injective inv := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_injective_dual_continuousH2_archimedean.solution

#print axioms groupCohomology.exists_injective_dual_continuousH2_archimedean

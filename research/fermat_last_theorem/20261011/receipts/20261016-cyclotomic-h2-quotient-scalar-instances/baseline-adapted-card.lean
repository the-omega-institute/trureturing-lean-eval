import Mathlib
import Submission.Supplier.Definitions.Def_GroupCohomology_ContinuousUnramified
import Submission.Supplier.Definitions.Def_DualSelmer_ExtConditions
import Submission.Supplier.Definitions.Def_ExtCitation_KummerBridge
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_groupCohomology_continuousH2S_ofChar_cycloChar_eq_zero_of_not_mem

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
attribute [-instance] AlgebraicClosure.Rat.isGalois

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Module groupCohomology ExtCitation

theorem groupCohomology.continuousH2S_ofChar_cycloChar_eq_zero_of_not_mem
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hp2 : p ≠ 2) (hpS : pPrime p ∉ S)
    (c : continuousH2S S (ofChar (k := ZMod p) (cycloChar p))) : c = 0 := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_continuousH2S_ofChar_cycloChar_eq_zero_of_not_mem.solution

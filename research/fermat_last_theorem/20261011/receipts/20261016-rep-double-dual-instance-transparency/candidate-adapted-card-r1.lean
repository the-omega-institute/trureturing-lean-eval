import Mathlib
import Submission.Supplier.Definitions.Def_DualSelmer_ExtConditions
import Submission.Supplier.Definitions.Def_ExtCitation_KummerBridge
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_Rep_nonempty_dualTwist_dualTwist_iso

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation
theorem Rep.nonempty_dualTwist_dualTwist_iso
    {p : ℕ} [Fact p.Prime] {Γ : Type} [Group Γ] (χ : Γ →* (ZMod p)ˣ)
    (M : Rep (ZMod p) Γ) [FiniteDimensional (ZMod p) M] :
    Nonempty ((M.dualTwist χ).dualTwist χ ≅ M) := by p2m_exact_reverting @_root_.P2MW.S_Rep_nonempty_dualTwist_dualTwist_iso.solution

#print axioms Rep.nonempty_dualTwist_dualTwist_iso

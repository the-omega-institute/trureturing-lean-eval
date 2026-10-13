import Mathlib
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_Rep_nonempty_invariants_coind_linearEquiv_invariants

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

universe u

open CategoryTheory
theorem Rep.nonempty_invariants_coind_linearEquiv_invariants {k G : Type u} [CommRing k] [Group G] (S : Subgroup G) (N : Rep.{u} k S) :
    Nonempty ((Rep.coind S.subtype N).ρ.invariants ≃ₗ[k] N.ρ.invariants) := by p2m_exact_reverting @_root_.P2MW.S_Rep_nonempty_invariants_coind_linearEquiv_invariants.solution

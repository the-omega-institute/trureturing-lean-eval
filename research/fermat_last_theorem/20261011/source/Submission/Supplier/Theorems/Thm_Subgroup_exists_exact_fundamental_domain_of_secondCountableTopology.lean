import Mathlib.Topology.Algebra.Group.Basic
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_Subgroup_exists_exact_fundamental_domain_of_secondCountableTopology

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

theorem Subgroup.exists_exact_fundamental_domain_of_secondCountableTopology
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    (Γ : Subgroup G) (hdisc : ∃ V : Set G, IsOpen V ∧ V ∩ (Γ : Set G) = {1}) :
    ∃ F : Set G,
      (∃ U C : ℕ → Set G, (∀ n, IsOpen (U n)) ∧ (∀ n, IsOpen (C n)) ∧ F = ⋃ n, U n \ C n) ∧
      ∀ x : G, ∃! γ : ↥Γ, (γ : G) * x ∈ F := by p2m_exact_reverting @_root_.P2MW.S_Subgroup_exists_exact_fundamental_domain_of_secondCountableTopology.solution

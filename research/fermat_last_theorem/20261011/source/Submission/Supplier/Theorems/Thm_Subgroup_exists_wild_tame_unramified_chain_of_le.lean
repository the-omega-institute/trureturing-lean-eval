import Mathlib
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_Subgroup_exists_wild_tame_unramified_chain_of_le

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false
universe u
open Module
theorem Subgroup.exists_wild_tame_unramified_chain_of_le
    {G : Type*} [Group G] {q : ℕ} [Fact q.Prime]
    (U W : Subgroup G) [U.Normal] [U.FiniteIndex] [W.Normal] (hUW : U ≤ W)
    (hWq : ∀ w ∈ W, ∃ a : ℕ, w ^ (q ^ a) ∈ U)
    (t φ : G) (hφt : (t ^ q)⁻¹ * (φ * t * φ⁻¹) ∈ W)
    (hgen : ∀ g : G, ∃ n : ℕ, (φ ^ n)⁻¹ * g ∈ Subgroup.closure {t} ⊔ W)
    (S H : Subgroup G) (hUH : U ≤ H) (hHS : H ≤ S) (hHn : (H.subgroupOf S).Normal) :
    ∃ P I : Subgroup G, H ≤ P ∧ P ≤ I ∧ I ≤ S ∧ (P.subgroupOf S).Normal ∧ (I.subgroupOf S).Normal ∧
      (∃ n : ℕ, (H.subgroupOf P).index = q ^ n) ∧ ¬ q ∣ (P.subgroupOf I).index ∧
      (∃ g ∈ S, ∀ s ∈ S, ∃ n : ℕ, (g ^ n)⁻¹ * s ∈ I) := by p2m_exact_reverting @_root_.P2MW.S_Subgroup_exists_wild_tame_unramified_chain_of_le.solution

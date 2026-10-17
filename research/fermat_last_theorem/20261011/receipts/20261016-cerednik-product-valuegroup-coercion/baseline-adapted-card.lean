import Submission.Supplier.Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_CerednikDrinfeld_Omega_exists_mem_holOn_hasProd_evalAt

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open Filter CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_mem_holOn_hasProd_evalAt
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K]
    {S : Set K} {ι : Type} (r : ι → RatPair K)
    (hpf : ∀ γ, (r γ).IsPoleFreeOn S)
    (hbd : ∀ γ, ∃ b : K, ∀ z ∈ S, Valued.v ((r γ).evalAt z) ≤ Valued.v b)
    (c : ℕ → K) (hc : ∀ n, c n ≠ 0) (hcof : ∀ y : K, y ≠ 0 → ∃ n, Valued.v (c n) ≤ Valued.v y)
    (E : ℕ → Finset ι) (hmono : Monotone E)
    (hE : ∀ n, ∀ γ, γ ∉ E n → ∀ z ∈ S, Valued.v ((r γ).evalAt z - 1) < Valued.v (c n)) :
    ∃ P : ↥S → K, P ∈ holOn K S ∧
      (∀ z : ↥S, HasProd (fun γ => (r γ).evalAt (z : K)) (P z)) ∧
      (∀ z : ↥S, P z = 0 ↔ ∃ γ, (r γ).evalAt (z : K) = 0) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_exists_mem_holOn_hasProd_evalAt.solution

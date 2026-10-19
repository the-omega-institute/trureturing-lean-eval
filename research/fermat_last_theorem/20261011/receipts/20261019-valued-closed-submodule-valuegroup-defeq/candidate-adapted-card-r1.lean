import Mathlib
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_Valued_isClosed_submodule_of_finiteDimensional_of_isClosed_subfield

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

theorem Valued.isClosed_submodule_of_finiteDimensional_of_isClosed_subfield
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (K₀' : Subfield K) (hcl : IsClosed (K₀' : Set K)) (hnt : ∃ x ∈ K₀', x ≠ 0 ∧ Valued.v x < 1)
    (V : Submodule ↥K₀' K) [FiniteDimensional ↥K₀' ↥V] :
    IsClosed (V : Set K) := by p2m_exact_reverting @_root_.P2MW.S_Valued_isClosed_submodule_of_finiteDimensional_of_isClosed_subfield.solution

#print axioms Valued.isClosed_submodule_of_finiteDimensional_of_isClosed_subfield

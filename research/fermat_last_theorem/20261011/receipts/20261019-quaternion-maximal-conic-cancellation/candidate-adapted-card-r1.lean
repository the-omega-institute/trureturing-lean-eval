import Mathlib
import Submission.Supplier.Definitions.Def_QuaternionAlgebra_EichlerOrder
import Submission.Supplier.Definitions.Def_QuaternionAlgebra_ReducedNorm
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_QuaternionAlgebra_IsMaximalOrder_exists_mem_padicValRat_nrd_eq_one_of_isDefiniteRamifiedExactlyAt

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false
open scoped Quaternion
open QuaternionAlgebra

theorem QuaternionAlgebra.IsMaximalOrder.exists_mem_padicValRat_nrd_eq_one_of_isDefiniteRamifiedExactlyAt
    {a b : ℚ} (q' : ℕ) [Fact q'.Prime] (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) :
    ∃ h ∈ Λ, h ≠ 0 ∧ padicValRat q' (QuaternionAlgebra.nrd h) = 1 := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_mem_padicValRat_nrd_eq_one_of_isDefiniteRamifiedExactlyAt.solution

#print axioms QuaternionAlgebra.IsMaximalOrder.exists_mem_padicValRat_nrd_eq_one_of_isDefiniteRamifiedExactlyAt

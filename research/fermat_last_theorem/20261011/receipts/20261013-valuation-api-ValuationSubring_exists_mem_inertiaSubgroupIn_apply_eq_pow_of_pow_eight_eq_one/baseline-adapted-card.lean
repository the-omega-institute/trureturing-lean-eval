import Submission.Supplier.Definitions.Def_FLTPrelim_Ramification
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_eight_eq_one

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

theorem ValuationSubring.exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_eight_eq_one
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime 2) (u : (ZMod 8)ˣ) :
    ∃ σ ∈ A.inertiaSubgroupIn ℚ, ∀ μ : AlgebraicClosure ℚ, μ ^ 8 = 1 →
      σ μ = μ ^ ((u : ZMod 8)).val := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_eight_eq_one.solution

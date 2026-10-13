import Submission.Supplier.Definitions.Def_FLTPrelim_Ramification
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_ValuationSubring_exists_mem_inertiaSubgroupIn_cycloChar_ne_one

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

theorem ValuationSubring.exists_mem_inertiaSubgroupIn_cycloChar_ne_one
    (q : ℕ) (hq : q.Prime) (m : ℕ) (hm : (Odd q ∧ m = q) ∨ (q = 2 ∧ m = 8))
    (cyc : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod m)ˣ)
    (hcyc : ∀ σ (μ : AlgebraicClosure ℚ), μ ^ m = 1 → σ μ = μ ^ ((cyc σ : ZMod m)).val)
    {K : Type} [Field K] (χ : (ZMod m)ˣ →* Kˣ) (hχ : χ ≠ 1) :
    ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q →
      ∃ σ ∈ A.inertiaSubgroupIn ℚ, χ (cyc σ) ≠ 1 := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_cycloChar_ne_one.solution

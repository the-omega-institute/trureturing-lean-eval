import Mathlib
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_Module_End_exists_ne_zero_forall_apply_eq_smul_of_dual_comp_eq_smul

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

theorem Module.End.exists_ne_zero_forall_apply_eq_smul_of_dual_comp_eq_smul
    {K : Type*} [Field K] {M : Type*} [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    {R : Type*} [CommRing R] (T : R →+* Module.End K M) (a : R →+* K)
    (μ : Module.Dual K M) (hμ : μ ≠ 0) (hco : ∀ r : R, μ ∘ₗ (T r : M →ₗ[K] M) = a r • μ) :
    ∃ m : M, m ≠ 0 ∧ ∀ r : R, T r m = a r • m := by p2m_exact_reverting @_root_.P2MW.S_Module_End_exists_ne_zero_forall_apply_eq_smul_of_dual_comp_eq_smul.solution

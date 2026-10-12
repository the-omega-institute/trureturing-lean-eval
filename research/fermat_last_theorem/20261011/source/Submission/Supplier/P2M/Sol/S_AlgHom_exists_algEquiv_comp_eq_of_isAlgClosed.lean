import Mathlib
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_AlgHom_exists_eq_comp_evalAlgHom_of_isDomain

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
namespace P2MW.S_AlgHom_exists_algEquiv_comp_eq_of_isAlgClosed

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000


theorem solution
    {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω]
    [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    {M : Type*} [Field M] [Algebra K M] (σ τ : M →ₐ[K] Ω) :
    ∃ γ : Ω ≃ₐ[K] Ω, γ.toAlgHom.comp σ = τ := by
  exact _root_.P2MW.S_AlgHom_exists_eq_comp_evalAlgHom_of_isDomain.W2G9.exists_algEquiv_comp_eq σ τ

end P2MW.S_AlgHom_exists_algEquiv_comp_eq_of_isAlgClosed

#print axioms _root_.P2MW.S_AlgHom_exists_algEquiv_comp_eq_of_isAlgClosed.solution

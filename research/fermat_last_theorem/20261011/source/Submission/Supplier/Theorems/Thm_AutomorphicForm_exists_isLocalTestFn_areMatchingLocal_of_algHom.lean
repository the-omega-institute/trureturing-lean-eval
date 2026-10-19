import Submission.Supplier.Definitions.Def_AutomorphicForm_TwistedOrbital
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_AutomorphicForm_exists_isLocalTestFn_areMatchingLocal_of_algHom

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

theorem AutomorphicForm.exists_isLocalTestFn_areMatchingLocal_of_algHom
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K)) (ι : L →ₐ[K] v.adicCompletion K)
    (φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (hφv : IsSemiLocalTestFn K L v φv) :
    ∃ fv : GL (Fin 2) (v.adicCompletion K) → ℂ, IsLocalTestFn K v fv ∧ AreMatchingLocal K L v σ φv fv := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_isLocalTestFn_areMatchingLocal_of_algHom.solution

#print axioms AutomorphicForm.exists_isLocalTestFn_areMatchingLocal_of_algHom

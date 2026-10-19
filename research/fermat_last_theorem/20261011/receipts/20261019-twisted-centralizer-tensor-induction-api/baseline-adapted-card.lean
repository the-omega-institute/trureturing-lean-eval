import Submission.Supplier.Definitions.Def_AutomorphicForm_TwistedOrbital
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_AutomorphicForm_twistedCentralizer_eq_map_centralizer_of_isNormConjugator_one

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open scoped TensorProduct

theorem AutomorphicForm.twistedCentralizer_eq_map_centralizer_of_isNormConjugator_one
    (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
    (hdeg : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (γ : GL (Fin 2) A) (hγ : AutomorphicForm.IsRegularSemisimple γ) (δ : GL (Fin 2) (L ⊗[K] A))
    (hN : AutomorphicForm.IsNormConjugator K L A σ γ δ 1) :
    AutomorphicForm.twistedCentralizer K L A σ δ =
      (Subgroup.centralizer {γ}).map (AutomorphicForm.toTensorGL K L A) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_twistedCentralizer_eq_map_centralizer_of_isNormConjugator_one.solution

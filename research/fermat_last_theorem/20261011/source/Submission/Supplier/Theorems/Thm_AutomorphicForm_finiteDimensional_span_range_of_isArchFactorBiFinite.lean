import Submission.Supplier.Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_AutomorphicForm_finiteDimensional_span_range_of_isArchFactorBiFinite

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open NumberField

theorem AutomorphicForm.finiteDimensional_span_range_of_isArchFactorBiFinite
    (F : Type) [Field F] (tys : ArchTypeFamily F) (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (hfa : IsArchFactorBiFinite F tys fa) (w : InfinitePlace F) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ w.Completion =>
        fun x : GL (Fin 2) (InfiniteAdeleRing F) => fa (x * archRowIsometryInclAt₀ F w k))) ∧
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ w.Completion =>
        fun x : GL (Fin 2) (InfiniteAdeleRing F) => fa (x * archRowIsometryInclAt₀ F w k)⁻¹)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_finiteDimensional_span_range_of_isArchFactorBiFinite.solution

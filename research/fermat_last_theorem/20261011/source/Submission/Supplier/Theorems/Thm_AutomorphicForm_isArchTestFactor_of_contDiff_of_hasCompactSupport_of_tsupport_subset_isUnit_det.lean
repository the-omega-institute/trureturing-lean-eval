import Submission.Supplier.Definitions.Def_AutomorphicForm_FactorizableTestFn
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_AutomorphicForm_isArchTestFactor_of_contDiff_of_hasCompactSupport_of_tsupport_subset_isUnit_det

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open NumberField
open scoped Classical in

theorem AutomorphicForm.isArchTestFactor_of_contDiff_of_hasCompactSupport_of_tsupport_subset_isUnit_det
    (F : Type) [Field F] [NumberField F] (Φ : (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F) → ℂ)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hc : HasCompactSupport Φ)
    (hU : tsupport Φ ⊆ {E | IsUnit (Matrix.det (Matrix.of E))}) :
    IsArchTestFactor F fun g => Φ (archEntries F g) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isArchTestFactor_of_contDiff_of_hasCompactSupport_of_tsupport_subset_isUnit_det.solution

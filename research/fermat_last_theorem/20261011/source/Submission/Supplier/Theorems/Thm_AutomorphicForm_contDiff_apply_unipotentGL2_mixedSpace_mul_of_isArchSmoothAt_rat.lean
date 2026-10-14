import Submission.Supplier.Definitions.Def_NumberField_AdelicBox
import Submission.Supplier.Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Submission.Supplier.Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Submission.Supplier.Definitions.Def_NumberField_AdelicLevel
import Submission.Supplier.Definitions.Def_M4aHerbrand_IdeleClassVocab
import Submission.Supplier.Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_AutomorphicForm_contDiff_apply_unipotentGL2_mixedSpace_mul_of_isArchSmoothAt_rat

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicBox NumberField.AdelicLevel AutomorphicForm

open scoped Classical in

theorem AutomorphicForm.contDiff_apply_unipotentGL2_mixedSpace_mul_of_isArchSmoothAt_rat
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hsm : IsArchSmoothAt Rat.isReal_infinitePlace φ)
    (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    ContDiff ℝ (Module.finrank ℚ ℚ + 1) (fun z : mixedEmbedding.mixedSpace ℚ =>
      φ (unipotentGL2 (R := AdeleRing (𝓞 ℚ) ℚ)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm z, 0) * g)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_contDiff_apply_unipotentGL2_mixedSpace_mul_of_isArchSmoothAt_rat.solution

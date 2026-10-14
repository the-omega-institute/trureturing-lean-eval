import Submission.Supplier.Definitions.Def_AutomorphicForm_CuspidalConstituent
import Submission.Supplier.Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_AutomorphicForm_CuspidalConstituent_continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open NumberField NumberField.AdelicBox AutomorphicForm AutomorphicForm.CuspidalConstituent IsDedekindDomain

theorem AutomorphicForm.CuspidalConstituent.continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K)) (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K))
    (gen : HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K)
    (ξ : (productionPinsOf K D U gen (adelicBox K)).Z →* ℂˣ)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hx : x ∈ cuspKFiniteSubmodule K (productionPinsOf K D U gen (adelicBox K)) ξ) :
    Continuous x ∧ ∀ g : AdelicGL2 (𝓞 K) K,
      IsSmoothCuspAutomorphicFnAt K (productionPinsOf K D U gen (adelicBox K)) ξ (rightTranslate K g x) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_CuspidalConstituent_continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule.solution

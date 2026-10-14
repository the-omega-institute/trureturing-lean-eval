import Submission.Supplier.Definitions.Def_AutomorphicForm_CuspidalConstituent
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_AutomorphicForm_CuspidalConstituent_exists_subset_iSupIndep_iSup_eq_of_finset_isCuspConstituent

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.exists_subset_iSupIndep_iSup_eq_of_finset_isCuspConstituent
    (F : Type) [Field F] [NumberField F] (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    (𝒱 : Finset (Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)))
    (h𝒱 : ∀ V ∈ 𝒱, IsCuspConstituent F pins ξ V) :
    ∃ 𝒲 : Finset (Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)), 𝒲 ⊆ 𝒱 ∧
      iSupIndep (fun W : ↥𝒲 => (W : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))) ∧
      (⨆ W ∈ 𝒲, W) = ⨆ V ∈ 𝒱, V := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_CuspidalConstituent_exists_subset_iSupIndep_iSup_eq_of_finset_isCuspConstituent.solution

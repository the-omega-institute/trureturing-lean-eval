import Submission.Supplier.Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Submission.Supplier.Definitions.Def_AutomorphicForm_FactorizableTestFn
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_AutomorphicForm_exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm IsDedekindDomain

theorem AutomorphicForm.exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact
    (F : Type) [Field F] [NumberField F]
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (fa₀ : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (hfa₀ : IsArchTestFactor F fa₀)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ) (hff : IsFinTestFactor F ff) (g₀ : AdelicGL2 (𝓞 F) F)
    (hg₀ : rightConv F φ (fun g => fa₀ (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g₀ ≠ 0)
    (C : Set (AdelicGL2 (𝓞 F) F)) (hC : IsCompact C) (η : ℝ) (hη : 0 < η) :
    ∃ (tys : ArchTypeFamily F) (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ),
      IsArchTestFactor F fa ∧ IsArchFactorBiFinite F tys fa ∧
        rightConv F φ (fun g => fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) ≠ 0 ∧
        rightConv F φ (fun g => fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) ∈ archCutSubmodule F tys ∧
        ∀ g ∈ C, ‖rightConv F φ (fun g => fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g -
            rightConv F φ (fun g => fa₀ (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g)) g‖ ≤ η := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_isArchFactorBiFinite_rightConv_ne_zero_and_norm_sub_le_of_isCompact.solution

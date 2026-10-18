import Submission.Supplier.Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_AutomorphicForm_IsKfSmooth_exists_isCompact_isOpen_eq_inf_forall_apply_mul_eq

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
attribute [-simp] AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm

theorem AutomorphicForm.IsKfSmooth.exists_isCompact_isOpen_eq_inf_forall_apply_mul_eq
    (F : Type) [Field F] [NumberField F] (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsKfSmooth F φ) :
    ∃ (U : Subgroup (AdelicGL2 (𝓞 F) F)) (_ : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
      (O : Subgroup (AdelicGL2 (𝓞 F) F)) (_ : IsOpen (O : Set (AdelicGL2 (𝓞 F) F))),
      U = O ⊓ finiteAdelicGL2Subgroup F ∧ ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U, φ (g * k) = φ g := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_IsKfSmooth_exists_isCompact_isOpen_eq_inf_forall_apply_mul_eq.solution

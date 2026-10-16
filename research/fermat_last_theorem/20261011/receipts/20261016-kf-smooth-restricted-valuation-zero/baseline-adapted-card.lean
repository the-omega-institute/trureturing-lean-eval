import Submission.Supplier.Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_AutomorphicForm_IsKfSmooth_exists_ideal_forall_apply_mul_conj_unipotentGL2_eq

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

open NumberField NumberField.AdelicLevel

theorem AutomorphicForm.IsKfSmooth.exists_ideal_forall_apply_mul_conj_unipotentGL2_eq
    {F : Type} [Field F] [NumberField F] {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsKfSmooth F φ) :
    ∃ 𝔫 : Ideal (𝓞 F), 𝔫 ≠ ⊥ ∧
      ∀ (g x : AdelicGL2 (𝓞 F) F), glFin (𝓞 F) F x ∈ finiteIntegralGL2 (𝓞 F) F →
      ∀ (t : AdeleRing (𝓞 F) F), adeleArch (𝓞 F) F t = 0 →
        adeleFin (𝓞 F) F t ∈ idealBall (𝓞 F) F 𝔫 →
          φ (g * (x⁻¹ * unipotentGL2 t * x)) = φ g := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_IsKfSmooth_exists_ideal_forall_apply_mul_conj_unipotentGL2_eq.solution

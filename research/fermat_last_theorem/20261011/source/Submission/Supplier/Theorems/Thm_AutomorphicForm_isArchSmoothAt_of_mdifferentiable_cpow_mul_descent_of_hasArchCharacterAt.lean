import Submission.Supplier.Definitions.Def_AutomorphicForm_ArchLowestWeight
import Submission.Supplier.Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_AutomorphicForm_isArchSmoothAt_of_mdifferentiable_cpow_mul_descent_of_hasArchCharacterAt

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open NumberField AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped Manifold

theorem AutomorphicForm.isArchSmoothAt_of_mdifferentiable_cpow_mul_descent_of_hasArchCharacterAt
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (k : ℤ) (c₀ σ : ℂ)
    (hk : HasArchCharacterAt₀ F w (archWeightCharAt hw k) φ)
    (hc : ∀ t : ℝˣ, (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 F) F,
      φ (adelicArchGLInclAt F w
          (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
            (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g) = (((t : ℝ) : ℂ) ^ c₀) * φ g)
    (hσ : ∀ g : AdelicGL2 (𝓞 F) F, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) fun z : UpperHalfPlane =>
      (((z.im : ℝ) : ℂ) ^ σ) * φ (g * adelicArchGLInclAt F w
          (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
            (iwasawaSectionGL z)))) :
    IsArchSmoothAt hw φ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isArchSmoothAt_of_mdifferentiable_cpow_mul_descent_of_hasArchCharacterAt.solution

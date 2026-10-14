import Submission.Supplier.Definitions.Def_AutomorphicForm_ArchLowestWeight
import Submission.Supplier.Definitions.Def_AutomorphicForm_ArchLoweringAnnihilated
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_AutomorphicForm_isArchLowestWeightAt_iff_isArchLoweringAnnihilatedAt_of_hasArchCharacterAt

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

p2m_open "NumberField AutomorphicForm~mdifferentiable_im_cpow_mul_iff_forall_lowering_fderiv_eq NumberField.InfinitePlace NumberField.InfinitePlace.Completion"

theorem AutomorphicForm.isArchLowestWeightAt_iff_isArchLoweringAnnihilatedAt_of_hasArchCharacterAt
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsReal) (k : ℤ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (hk : HasArchCharacterAt₀ F w
      ((archWeightCharℝ k).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
        (norm_ringEquivRealOfIsReal hw))) φ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (hξ : ∀ (z : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ)) (g : AdelicGL2 (𝓞 F) F),
      φ (centralScalar (𝓞 F) F (z : (AdeleRing (𝓞 F) F)ˣ) * g) = ((ξ z : ℂˣ) : ℂ) * φ g) :
    IsArchLowestWeightAt w hw φ ↔ IsArchLoweringAnnihilatedAt w hw φ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isArchLowestWeightAt_iff_isArchLoweringAnnihilatedAt_of_hasArchCharacterAt.solution

import Submission.Supplier.Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_AutomorphicForm_exists_isSectionFn_and_isLocallyConstant_of_isRegularSemisimple_of_isLocalTestFn

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory TopologicalSpace

theorem AutomorphicForm.exists_isSectionFn_and_isLocallyConstant_of_isRegularSemisimple_of_isLocalTestFn
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (γ : GL (Fin 2) (v.adicCompletion K)) (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ))
    [@Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ]
    (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (hfv : AutomorphicForm.IsLocalTestFn K v fv) :
    ∃ w : GL (Fin 2) (v.adicCompletion K) → ℝ,
      AutomorphicForm.IsSectionFn K v γ τ fv w ∧ IsLocallyConstant w := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_isSectionFn_and_isLocallyConstant_of_isRegularSemisimple_of_isLocalTestFn.solution

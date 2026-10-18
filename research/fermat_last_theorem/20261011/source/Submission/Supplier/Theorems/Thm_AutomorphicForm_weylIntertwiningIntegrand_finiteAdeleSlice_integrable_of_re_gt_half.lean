import Submission.Supplier.Definitions.Def_AutomorphicForm_InducedSection
import Submission.Supplier.Definitions.Def_AutomorphicForm_EtaFamily
import Submission.Supplier.Definitions.Def_AutomorphicForm_WeylIntertwining
import Submission.Supplier.Definitions.Def_NumberField_AdelicHaar
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

open MeasureTheory NumberField IsDedekindDomain
open scoped NNReal

theorem AutomorphicForm.weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)]
    [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (σ : Measure (FiniteAdeleRing (𝓞 F) F))
    [σ.IsAddHaarMeasure] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ)
      (_hν : IsUnitaryChar (𝓞 F) F ν)
      (s : ℂ)
      (_hs : 1 / 2 < s.re)
      (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
      (_hφc : Continuous φ)
      (g : AdelicGL2 (𝓞 F) F),
    Integrable (fun t : FiniteAdeleRing (𝓞 F) F =>
      φ (adelicWeyl (𝓞 F) F * unipotentGL2 (R := AdeleRing (𝓞 F) F) (0, t) * g)) σ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.solution

#print axioms AutomorphicForm.weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half

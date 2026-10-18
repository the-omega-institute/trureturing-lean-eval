import Submission.Supplier.Definitions.Def_NumberField_AdelicHaar
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_NumberField_AdelicFourier_exists_smul_eq_of_isAddHaarMeasure_adeleRing

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
attribute [-instance] instCountableOfNumberField_definitions

open NumberField
theorem NumberField.AdelicFourier.exists_smul_eq_of_isAddHaarMeasure_adeleRing (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ ν : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure] :
    ∃ c : NNReal, 0 < c ∧ μ = c • ν := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicFourier_exists_smul_eq_of_isAddHaarMeasure_adeleRing.solution

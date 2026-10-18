import Submission.Supplier.Definitions.Def_NumberField_AdelicBox
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_NumberField_AdelicBox_inv_measure_adelicBox_mul_integral_pureTensor_eq

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
attribute [-instance] instCountableOfNumberField_definitions

set_option autoImplicit false

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.AdelicBox IsDedekindDomain
open scoped Classical in

theorem NumberField.AdelicBox.inv_measure_adelicBox_mul_integral_pureTensor_eq
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    (f : mixedEmbedding.mixedSpace F → ℂ) (g : FiniteAdeleRing (𝓞 F) F → ℂ) :
    ((μ (adelicBox F)).toReal : ℂ)⁻¹ *
        ∫ x, f (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * g x.2 ∂μ
      = (((2 : ℝ) ^ nrComplexPlaces F / Real.sqrt |(discr F : ℝ)| : ℝ) : ℂ) *
        ((∫ y, f y) * (((ν (integralFiniteAdeles (𝓞 F) F)).toReal : ℂ)⁻¹ * ∫ z, g z ∂ν)) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicBox_inv_measure_adelicBox_mul_integral_pureTensor_eq.solution

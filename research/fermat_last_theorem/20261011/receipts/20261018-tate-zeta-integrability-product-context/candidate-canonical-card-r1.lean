import Definitions.Def_NumberField_TateGlobalZeta
import P2M.Util
import P2M.Sol.S_NumberField_TateGlobal_integrable_zetaIntegrand
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_submission NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_submission instLocallyCompactSpaceAdicCompletionRingOfIntegers_submission IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal instCountableOfNumberField_submission
attribute [-simp] LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicFourier AutomorphicForm

theorem NumberField.TateGlobal.integrable_zetaIntegrand (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure]
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ schwartzBruhat F)
    {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hχc : Continuous χ) (hχu : IsUnitaryChar (𝓞 F) F χ)
    {s : ℂ} (hs : 1 < s.re) :
    Integrable (fun x : (AdeleRing (𝓞 F) F)ˣ => f x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s) ν := by p2m_exact_reverting @_root_.P2MW.S_NumberField_TateGlobal_integrable_zetaIntegrand.solution

#print axioms NumberField.TateGlobal.integrable_zetaIntegrand

import Submission.Supplier.Definitions.Def_NumberField_AdelicBox
import Submission.Supplier.Definitions.Def_LanglandsTunnell_TateLocalZeta
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_AutomorphicForm_LocalIntertwining_integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_submission NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_submission instLocallyCompactSpaceAdicCompletionRingOfIntegers_submission IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal instCountableOfNumberField_submission

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

theorem AutomorphicForm.LocalIntertwining.integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μ : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)) [∀ v, (μ v).IsAddHaarMeasure]
    (h : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F → ℂ)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ)
    (hϖ : ∀ v ∉ S, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∀ v ∉ S, ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ v u = 1)
    (hχ₁ : ∀ v ∉ S, ‖((χ v (ϖ v) : ℂˣ) : ℂ)‖ ≤ 1)
    (s : ℂ) (hs : 1 / 2 < s.re) :
    (ν.real (NumberField.AdelicBox.integralFiniteAdeles (𝓞 F) F) : ℂ)⁻¹
        * (∫ x, (∏ v ∈ S, h v (x v))
              * ∏ᶠ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
                  (((v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F)).indicator
                      (fun _ => (1 : ℂ)) (x v.1)
                    + (v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F))ᶜ.indicator
                        (fun y => LanglandsTunnell.TateLocal.charExt (χ v.1)⁻¹ y
                          * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) (x v.1))) ∂ν)
        * ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
            (1 - ((χ v.1 (ϖ v.1) : ℂˣ) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s)))
      = (∏ v ∈ S, (((μ v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ)⁻¹
            * ∫ y, h v y ∂(μ v)))
        * ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
            (1 - ((χ v.1 (ϖ v.1) : ℂˣ) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_LocalIntertwining_integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod.solution

#print axioms AutomorphicForm.LocalIntertwining.integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod

import Submission.Supplier.Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_ModularCurve_correspondence_heckeBetaC_heckeAlphaC_correspondence_heckeBetaC_heckeAlphaC_comm

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply
attribute [-simp] ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply
set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.correspondence_heckeBetaC_heckeAlphaC_correspondence_heckeBetaC_heckeAlphaC_comm
    (N ℓ ℓ' q' : ℕ) [NeZero N] (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) [Fact q'.Prime]
    (hℓq' : ℓ ≠ q') (hℓ'q' : ℓ' ≠ q') (hq'N : ¬ q' ∣ N)
    {k : Type*} [Field k] [CharP k q'] [IsAlgClosed k] :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    haveI : NeZero ℓ' := ⟨hℓ'.ne_zero⟩
    ∀ [HasPrincipalDivisors k ↥(charLDegeneracyRoof k N ℓ)]
      [HasPrincipalDivisors k ↥(charLDegeneracyRoof k N ℓ')]
      (hα : HeckeAlphaCIntegral k N ℓ) (hβ : HeckeBetaCIntegral k N ℓ)
      (hα' : HeckeAlphaCIntegral k N ℓ') (hβ' : HeckeBetaCIntegral k N ℓ')
      (D : Divisor k ↥(modularFunctionFieldC k N)),
      Divisor.correspondence (heckeBetaC k N ℓ) (heckeAlphaC k N ℓ) hβ hα
          (Divisor.correspondence (heckeBetaC k N ℓ') (heckeAlphaC k N ℓ') hβ' hα' D)
        = Divisor.correspondence (heckeBetaC k N ℓ') (heckeAlphaC k N ℓ') hβ' hα'
            (Divisor.correspondence (heckeBetaC k N ℓ) (heckeAlphaC k N ℓ) hβ hα D) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_correspondence_heckeBetaC_heckeAlphaC_correspondence_heckeBetaC_heckeAlphaC_comm.solution

#print axioms ModularCurve.correspondence_heckeBetaC_heckeAlphaC_correspondence_heckeBetaC_heckeAlphaC_comm

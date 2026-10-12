import Mathlib
import Submission.Supplier.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Submission.Supplier.Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Submission.Supplier.Definitions.Def_AlgebraicCurve_IsCurveOver
import Submission.Supplier.Definitions.Def_ModularCurve_CanonicalDivisor
import Submission.Supplier.Definitions.Def_ModularCurve_CanonicalDivisorUniformizer
import Submission.Supplier.Definitions.Def_AlgebraicCurve_Repartitions
import Submission.Supplier.Definitions.Def_AlgebraicCurve_AdelicIndex
import Submission.Supplier.Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Submission.Supplier.Definitions.Def_AlgebraicCurve_LocalResidue
import Submission.Supplier.Definitions.Def_AlgebraicCurve_DivisorPushPull
import Submission.Supplier.Definitions.Def_DedekindDomain_AdicValuation_InlineSpecific
import Submission.Supplier.Definitions.Def_AlgebraicCurve_PlaceCompletion
import Submission.Supplier.Definitions.Def_AlgebraicCurve_TateResidueCurrency
import Submission.Supplier.Definitions.Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_AlgebraicCurve_residueTraceCompletionCommute_v2

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal

theorem AlgebraicCurve.residueTraceCompletionCommute_v2
    {K F E : Type*} [Field K] [Field F] [Algebra K F]
    [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
    [Algebra.IsIntegral E F]
    [∀ u : AlgebraicCurve.Place K E, u.FiniteResidue]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.IsCurveOver K E] [PerfectField K]
    [Nontrivial Ω[F⁄K]] [∀ w : AlgebraicCurve.Place K F, w.DCoordGenerates]
    [Algebra.IsSeparable E F] :
    ModularCurve.KwF4R1V391a.KwF4R1V391aResidueTraceCompletionCommute K F E := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_residueTraceCompletionCommute_v2.solution

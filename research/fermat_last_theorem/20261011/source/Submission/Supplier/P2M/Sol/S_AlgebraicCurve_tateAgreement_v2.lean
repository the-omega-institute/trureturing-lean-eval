import Submission.Supplier.P2M.Sol.S_AlgebraicCurve_tateAgreement
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

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
attribute [-ext] IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext
namespace P2MW.S_AlgebraicCurve_tateAgreement_v2

set_option autoImplicit false

noncomputable section

theorem solution
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [AlgebraicCurve.IsCurveOver K L] [PerfectField K]
    [∀ u : AlgebraicCurve.Place K L, u.FiniteResidue]
    (hfin : ModularCurve.KwF4gRRTate.KwF4gRRTateCommFinite K L) :
    ModularCurve.KwF4gRRTate.KwF4gRRTateAgreement K L hfin := by
  exact _root_.P2MW.S_AlgebraicCurve_tateAgreement.solution hfin

#print axioms solution

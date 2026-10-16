import Submission.Supplier.Definitions.Def_DedekindDomain_Completion_BaseChange
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_IsDedekindDomain_HeightOneSpectrum_exists_algebraMap_eq_mul_sq_adicCompletion

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
attribute [-instance] instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped Polynomial

theorem IsDedekindDomain.HeightOneSpectrum.exists_algebraMap_eq_mul_sq_adicCompletion
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (d : v.adicCompletion K) (hd : d ≠ 0) :
    ∃ (d' : K) (c : v.adicCompletion K), c ≠ 0 ∧ algebraMap K (v.adicCompletion K) d' = d * c ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_IsDedekindDomain_HeightOneSpectrum_exists_algebraMap_eq_mul_sq_adicCompletion.solution

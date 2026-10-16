import Definitions.Def_DedekindDomain_Completion_BaseChange
import P2M.Util
import P2M.Sol.S_IsDedekindDomain_HeightOneSpectrum_exists_algebraMap_eq_mul_sq_adicCompletion
attribute [-instance] instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_submission NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_submission instLocallyCompactSpaceAdicCompletionRingOfIntegers_submission instCountableOfNumberField_submission

set_option autoImplicit false

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped Polynomial

theorem IsDedekindDomain.HeightOneSpectrum.exists_algebraMap_eq_mul_sq_adicCompletion
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (d : v.adicCompletion K) (hd : d ≠ 0) :
    ∃ (d' : K) (c : v.adicCompletion K), c ≠ 0 ∧ algebraMap K (v.adicCompletion K) d' = d * c ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_IsDedekindDomain_HeightOneSpectrum_exists_algebraMap_eq_mul_sq_adicCompletion.solution

#print axioms IsDedekindDomain.HeightOneSpectrum.exists_algebraMap_eq_mul_sq_adicCompletion

import Mathlib
import P2M.Util
import P2M.Sol.S_IsDedekindDomain_HeightOneSpectrum_natCard_adicCompletionIntegers_rat_quotient_span_natCast_eq_prime_pow_factorization
attribute [-instance] IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal

set_option autoImplicit false

theorem IsDedekindDomain.HeightOneSpectrum.natCard_adicCompletionIntegers_rat_quotient_span_natCast_eq_prime_pow_factorization
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hℓv : (ℓ : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal) (n : ℕ) (hn : n ≠ 0) :
    Nat.card (v.adicCompletionIntegers ℚ ⧸ Ideal.span {(n : v.adicCompletionIntegers ℚ)}) =
      ℓ ^ n.factorization ℓ := by p2m_exact_reverting @_root_.P2MW.S_IsDedekindDomain_HeightOneSpectrum_natCard_adicCompletionIntegers_rat_quotient_span_natCast_eq_prime_pow_factorization.solution

#print axioms IsDedekindDomain.HeightOneSpectrum.natCard_adicCompletionIntegers_rat_quotient_span_natCast_eq_prime_pow_factorization

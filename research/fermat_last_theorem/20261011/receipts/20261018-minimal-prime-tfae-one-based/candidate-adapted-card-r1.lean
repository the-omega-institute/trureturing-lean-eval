import Mathlib
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_Ideal_not_isMaximal_of_mem_minimalPrimes_of_forall_not_isOpen_singleton

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open TensorProduct

theorem Ideal.not_isMaximal_of_mem_minimalPrimes_of_forall_not_isOpen_singleton
    {R : Type*} [CommRing R] {κ : Type*} [Field κ] [Algebra R κ]
    (ϖ : R) (hϖ : algebraMap R κ ϖ = 0) (hmax : (Ideal.span {ϖ}).IsMaximal)
    {B : Type*} [CommRing B] [Algebra R B] [Algebra.FiniteType R B] (b : B) (hb : b = algebraMap R B ϖ)
    (hiso : ∀ z : PrimeSpectrum (B ⊗[R] κ), ¬ IsOpen ({z} : Set (PrimeSpectrum (B ⊗[R] κ))))
    (Q : Ideal (B ⧸ Ideal.span {b})) (hQ : Q ∈ minimalPrimes (B ⧸ Ideal.span {b})) :
    ¬ Q.IsMaximal := by p2m_exact_reverting @_root_.P2MW.S_Ideal_not_isMaximal_of_mem_minimalPrimes_of_forall_not_isOpen_singleton.solution

#print axioms Ideal.not_isMaximal_of_mem_minimalPrimes_of_forall_not_isOpen_singleton

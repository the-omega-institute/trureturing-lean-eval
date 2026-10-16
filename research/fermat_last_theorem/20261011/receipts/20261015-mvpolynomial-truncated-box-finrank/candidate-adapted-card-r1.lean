import Mathlib
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_MvPolynomial_finrank_quotient_span_range_X_pow_eq_prod

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

universe u v

theorem MvPolynomial.finrank_quotient_span_range_X_pow_eq_prod
    (k : Type u) [CommRing k] [Nontrivial k] {ι : Type v} [Fintype ι] (N : ι → ℕ) :
    Module.finrank k (MvPolynomial ι k ⧸
      Ideal.span (Set.range fun i : ι => (MvPolynomial.X i : MvPolynomial ι k) ^ N i)) = ∏ i, N i := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_finrank_quotient_span_range_X_pow_eq_prod.solution

#print axioms MvPolynomial.finrank_quotient_span_range_X_pow_eq_prod

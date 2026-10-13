import Mathlib
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_Polynomial_abv_eval_le_gaussNorm

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open Polynomial

theorem Polynomial.abv_eval_le_gaussNorm {R : Type*} [CommRing R] (v : AbsoluteValue R ℝ)
    (hv : IsNonarchimedean v) {c : ℝ} (hc : 0 ≤ c) (p : R[X]) {z : R} (hz : v z ≤ c) :
    v (p.eval z) ≤ p.gaussNorm v c := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_abv_eval_le_gaussNorm.solution

#print axioms Polynomial.abv_eval_le_gaussNorm

import Mathlib
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_Polynomial_log_abv_eval_eq_log_gaussNorm_add_sum

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open Polynomial

theorem Polynomial.log_abv_eval_eq_log_gaussNorm_add_sum {K : Type*} [Field K] [IsAlgClosed K]
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v) (p : K[X]) (hp : p ≠ 0)
    {z : K} (hz : v z ≤ 1) (hpz : p.eval z ≠ 0) :
    Real.log (v (p.eval z)) = Real.log (p.gaussNorm v 1)
      + ((p.roots.filter fun a => v a ≤ 1).map fun a => Real.log (v (z - a))).sum := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_log_abv_eval_eq_log_gaussNorm_add_sum.solution

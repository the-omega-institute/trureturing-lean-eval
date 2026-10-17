import Submission.Supplier.Definitions.Def_MvPolynomial_LogMahlerMeasure
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_MvPolynomial_integrableOn_log_norm_eval_circleMap

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

theorem MvPolynomial.integrableOn_log_norm_eval_circleMap {n : ℕ} (P : MvPolynomial (Fin n) ℂ) :
    MeasureTheory.IntegrableOn
      (fun θ : Fin n → ℝ ↦ Real.log ‖MvPolynomial.eval (fun i ↦ circleMap 0 1 (θ i)) P‖)
      (MvPolynomial.torusBox n) := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_integrableOn_log_norm_eval_circleMap.solution

#print axioms MvPolynomial.integrableOn_log_norm_eval_circleMap

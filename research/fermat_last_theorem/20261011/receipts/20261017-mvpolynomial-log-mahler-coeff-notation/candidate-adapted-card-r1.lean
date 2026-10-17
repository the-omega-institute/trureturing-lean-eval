import Submission.Supplier.Definitions.Def_MvPolynomial_LogMahlerMeasure
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_MvPolynomial_log_norm_coeff_le_logMahlerMeasure_add

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false

local macro "MvPolynomial.coeff" d:term:arg P:term:arg : term =>
  `(AddMonoidAlgebra.coeff $P $d)
local macro "MvPolynomial.coeff" d:term:arg : term =>
  `(fun P => AddMonoidAlgebra.coeff P $d)
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

theorem MvPolynomial.log_norm_coeff_le_logMahlerMeasure_add {n : ℕ} (P : MvPolynomial (Fin n) ℂ) {m : Fin n →₀ ℕ} (hm : m ∈ P.support) :
    Real.log ‖MvPolynomial.coeff m P‖ ≤
      P.logMahlerMeasure + (∑ i, (MvPolynomial.degreeOf i P : ℝ)) * Real.log 2 := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_log_norm_coeff_le_logMahlerMeasure_add.solution

#print axioms MvPolynomial.log_norm_coeff_le_logMahlerMeasure_add

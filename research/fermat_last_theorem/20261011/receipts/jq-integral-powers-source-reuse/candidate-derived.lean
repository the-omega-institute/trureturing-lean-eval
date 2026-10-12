import Submission.Supplier.P2M.Sol.S_ModularCurve_PhiGen_aeval_jq_intCoeffs_descent

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

namespace P2MW.S_ModularCurve_PhiGen_intCoeffs_jq_pow

set_option autoImplicit false

noncomputable section

open _root_.ModularCurve _root_.ModularCurve.PhiGen

theorem solution (n : ℕ) : IntCoeffs (jq ^ n) := by
  exact _root_.P2MW.S_ModularCurve_PhiGen_aeval_jq_intCoeffs_descent.ModularCurve.PhiGen.intCoeffs_jq_pow n

end

#print axioms solution

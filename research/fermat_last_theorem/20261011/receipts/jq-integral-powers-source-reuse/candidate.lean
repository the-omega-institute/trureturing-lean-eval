import P2M.Sol.S_ModularCurve_PhiGen_aeval_jq_intCoeffs_descent

namespace P2MW.S_ModularCurve_PhiGen_intCoeffs_jq_pow

set_option autoImplicit false

noncomputable section

open _root_.ModularCurve _root_.ModularCurve.PhiGen

theorem solution (n : ℕ) : IntCoeffs (jq ^ n) := by
  exact _root_.P2MW.S_ModularCurve_PhiGen_aeval_jq_intCoeffs_descent.ModularCurve.PhiGen.intCoeffs_jq_pow n

end

#print axioms solution

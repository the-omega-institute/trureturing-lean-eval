import Submission.Supplier.P2M.Sol.S_ModularCurve_PhiGen_phiProd_conj_coeff_eq_zero_of_le

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

namespace P2MW.S_ModularCurve_PhiGen_tPoleOrderLE_phiProd_conj_of_ne_zero

set_option autoImplicit false

noncomputable section

open _root_.ModularCurve _root_.ModularCurve.PhiGen

theorem solution {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ) (k : ℕ) (hk : k ≠ 0) : TPoleOrderLE ((phiProd ℓ (conj ℓ ζ)).coeff k) (ℓ * ℓ + ℓ - 1) := by
  exact _root_.P2MW.S_ModularCurve_PhiGen_phiProd_conj_coeff_eq_zero_of_le.ModularCurve.PhiGen.tPoleOrderLE_phiProd_conj_of_ne_zero ℓ ζ k hk

end

#print axioms solution

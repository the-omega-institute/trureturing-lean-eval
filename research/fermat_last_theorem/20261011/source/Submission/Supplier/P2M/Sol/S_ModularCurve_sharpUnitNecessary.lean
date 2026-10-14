import Submission.Supplier.Theorems.Thm_ModularCurve_sharpUnitNecessary_of_prime
import Submission.Supplier.Theorems.Thm_ModularCurve_sharpUnitNecessary_of_mod_twelve_eq_one
import Submission.Supplier.P2M.Util

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
namespace P2MW.S_ModularCurve_sharpUnitNecessary

theorem solution (ℓ : ℕ) [Fact (Nat.Prime ℓ)] : ModularCurve.SharpUnitNecessary ℓ := by
  by_cases h : ℓ % 12 = 1
  · exact ModularCurve.sharpUnitNecessary_of_mod_twelve_eq_one ℓ h
  · exact ModularCurve.sharpUnitNecessary_of_prime ℓ h

import Submission.Supplier.Definitions.Def_ModularCurve_EtaQuotient
import Submission.Supplier.Definitions.Def_NumberTheory_DedekindSum
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_ModularCurve_sharpUnitNecessary_of_witness

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

theorem ModularCurve.sharpUnitNecessary_of_witness (ℓ : ℕ) [NeZero ℓ] (hℓ : 2 ≤ ℓ) (a d : ℤ) (c' : ℕ) (hc' : 0 < c') (h1 : Int.ModEq ((ℓ * c' : ℕ) : ℤ) (a * d) 1) (z₀ : ℤ) (hδ : 12 * (((a + d : ℤ) : ℚ) * (1 - (ℓ : ℚ)) / (12 * ((ℓ * c' : ℕ) : ℚ)) + dedekindSum d c' - dedekindSum d (ℓ * c')) = ((Nat.gcd (ℓ - 1) 12 : ℕ) : ℚ) * z₀) (hcop : Nat.Coprime z₀.natAbs (ModularCurve.eisensteinNumerator ℓ)) : ModularCurve.SharpUnitNecessary ℓ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_sharpUnitNecessary_of_witness.solution

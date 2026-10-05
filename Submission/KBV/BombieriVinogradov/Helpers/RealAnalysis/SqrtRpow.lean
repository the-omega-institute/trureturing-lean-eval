-- Vendored from kimihiro64/bombieri-vinogradov@7a174830 BombieriVinogradov/Helpers/RealAnalysis/SqrtRpow.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Basic.Real.Basic
/-!
# Real powers of a nonnegative square root

This exact normalization separates square-root algebra from limit arguments.
-/

set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

/-- Doubling a real exponent on a nonnegative square root removes the square root. -/
theorem sqrt_rpow_twice {t : Real} (ht : 0 <= t) (b : Real) :
    (Real.sqrt t) ^ (2 * b) = t ^ b := by
  rw [Real.rpow_mul (Real.sqrt_nonneg t), Real.rpow_two, Real.sq_sqrt ht]

end BombieriVinogradov.RealAnalysis

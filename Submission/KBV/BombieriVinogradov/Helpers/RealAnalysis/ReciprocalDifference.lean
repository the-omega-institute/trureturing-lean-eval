-- Vendored from kimihiro64/bombieri-vinogradov@7a174830 BombieriVinogradov/Helpers/RealAnalysis/ReciprocalDifference.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Consecutive reciprocal differences

Scalar normalization for the discrete reciprocal Abel kernel.
-/

set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

/-- The difference of adjacent reciprocal weights has a product denominator. -/
theorem mul_sub_reciprocal_eq_div_mul (a x : Real)
    (hx : Ne x 0) (hxOne : Ne (x + 1) 0) :
    a * (1 / x - 1 / (x + 1)) = a / (x * (x + 1)) := by
  field_simp
  ring

end BombieriVinogradov.RealAnalysis

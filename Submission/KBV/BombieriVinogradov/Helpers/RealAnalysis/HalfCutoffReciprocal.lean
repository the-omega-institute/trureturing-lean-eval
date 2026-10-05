-- Vendored from kimihiro64/bombieri-vinogradov@7a174830 BombieriVinogradov/Helpers/RealAnalysis/HalfCutoffReciprocal.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Reciprocal comparison at a half-size cutoff

A positive real cutoff that retains half the original size loses at most
a factor two in its reciprocal.
-/

set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

/-- Normalize the doubled inverse-cutoff contribution. -/
theorem two_mul_div_le_of_half_le {T r X : Real}
    (hT : 0 < T) (hCut : T / 2 <= r) (hX : 0 <= X) :
    2 * X / r <= 4 * X / T := by
  calc
    2 * X / r <= 2 * X / (T / 2) :=
      div_le_div_of_nonneg_left (a := 2 * X) (b := r) (c := T / 2)
        (by positivity) (by positivity) hCut
    _ = 4 * X / T := by ring

end BombieriVinogradov.RealAnalysis

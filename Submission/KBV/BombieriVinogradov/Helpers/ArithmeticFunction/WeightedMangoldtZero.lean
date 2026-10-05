-- Vendored from kimihiro64/bombieri-vinogradov@7a174830 BombieriVinogradov/Helpers/ArithmeticFunction/WeightedMangoldtZero.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
import Submission.KBV.BombieriVinogradov.Definitions.WeightedBombieriVinogradov
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# Empty-endpoint Mangoldt sums

Both global and residue-class sums vanish at the natural endpoint zero.
-/
set_option autoImplicit false

namespace BombieriVinogradov.WeightedBombieriVinogradov

theorem psiGlobal_zero : psiGlobal 0 = 0 := by
  simp [psiGlobal]

theorem psiProgression_zero (N : Nat) (a : ZMod N) : psiProgression 0 N a = 0 := by
  simp [psiProgression]

end BombieriVinogradov.WeightedBombieriVinogradov

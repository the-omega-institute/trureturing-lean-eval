-- Vendored from kimihiro64/bombieri-vinogradov@7a174830 BombieriVinogradov/Proof/SiegelWalfisz/ExplicitFormula/Centered/OptimizedCenteringScale.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Optimize.Definitions
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Optimize.Line
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Optimized centering scale

This module evaluates the reciprocal distance from the optimized Perron line
to one.
-/
set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The unit-point centering cost on the optimized line is exactly log x. -/
theorem one_div_optimizedPerronLine_sub_one
    {x : Nat} (hx : 2 < x) :
    1 / (optimizedPerronLine x - 1) = Real.log (x : Real) := by
  have hLogPos : 0 < Real.log (x : Real) :=
    lt_of_lt_of_le zero_lt_one (one_le_log_natCast hx)
  have hLogNe : Ne (Real.log (x : Real)) 0 := ne_of_gt hLogPos
  unfold optimizedPerronLine
  field_simp [hLogNe]
  ring

end BombieriVinogradov.SiegelWalfisz

-- Vendored from kimihiro64/bombieri-vinogradov@7a174830 BombieriVinogradov/Helpers/RealAnalysis/LogarithmicThreshold.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Monotonicity of logarithmic exceptional thresholds

Increasing a level narrows its exceptional window without changing the
positive absolute constant.
-/
set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

theorem logarithmicThreshold_mono {c d n : Real} (hc : 0 <= c)
    (hd : 1 < d) (hdn : d <= n) :
    1 - c / Real.log d <= 1 - c / Real.log n := by
  have hdPos : 0 < d := by linarith
  have hLogPos : 0 < Real.log d := Real.log_pos hd
  have hLogMono : Real.log d <= Real.log n := Real.log_le_log hdPos hdn
  have hDiv : c / Real.log n <= c / Real.log d :=
    div_le_div_of_nonneg_left hc hLogPos hLogMono
  linarith

end BombieriVinogradov.RealAnalysis

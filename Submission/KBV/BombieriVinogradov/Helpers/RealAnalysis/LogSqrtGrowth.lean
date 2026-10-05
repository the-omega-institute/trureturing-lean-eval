-- Vendored from kimihiro64/bombieri-vinogradov@7a174830 BombieriVinogradov/Helpers/RealAnalysis/LogSqrtGrowth.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# A square-root majorant for logarithmic growth

The logarithm inequality at the positive square root gives a simple
uniform bound suitable for explicit power-versus-exponential cutoffs.
-/
set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

theorem log_le_two_mul_sqrt {t : Real} (ht : 0 < t) :
    Real.log t <= 2 * Real.sqrt t := by
  have hRoot : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hBound := Real.log_le_sub_one_of_pos hRoot
  have hLogRoot := Real.log_sqrt ht.le
  linarith

end BombieriVinogradov.RealAnalysis

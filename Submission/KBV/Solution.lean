-- Vendored from kimihiro64/bombieri-vinogradov@7a174830 Solution.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
import Submission.KBV.BombieriVinogradov.Assembly.PrimeCountingConversion.Main
import Submission.KBV.BombieriVinogradov.Definitions.Statement
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.PrimeCounting

set_option autoImplicit false

/-!
# Bombieri--Vinogradov solution boundary

The theorem type is the exact consumer-facing proposition. Its proof is
supplied by the checked prime-counting assembly.
-/

namespace BombieriVinogradov

theorem bombieriVinogradov : _root_.KBVBombieriVinogradov := by
  exact PrimeCountingConversion.weighted_to_prime_counting

end BombieriVinogradov

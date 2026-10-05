-- Vendored from kimihiro64/bombieri-vinogradov@7a174830 BombieriVinogradov/Definitions/PrimeCounting.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.PrimeCounting
public import Submission.PNT.PrimeNumberTheoremAnd.Defs

/-!
# Prime counts in arithmetic progressions

This module defines the inclusive prime-counting functions used in Maynard's
equation (1.3) and in the downstream `PrimeGapsLib` challenge surface.
-/

set_option autoImplicit false

@[expose] public section

/-- The number of primes `p <= x` whose image in `ZMod q` is `a`. -/
noncomputable def Real.kbvPrimeCountingZMod (x : ℝ) (q : ℕ) (a : ZMod q) : ℕ :=
  {p : ℕ | p.Prime ∧ (p : ZMod q) = a ∧ p ≤ x}.ncard

namespace BombieriVinogradov

/-- The number of primes at most the real cutoff `x`, coerced to `Real`. -/
noncomputable def primeCounting (x : ℝ) : ℝ :=
  pi x

end BombieriVinogradov

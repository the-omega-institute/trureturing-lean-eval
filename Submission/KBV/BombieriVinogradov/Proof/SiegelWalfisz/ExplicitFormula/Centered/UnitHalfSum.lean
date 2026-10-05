-- Vendored from kimihiro64/bombieri-vinogradov@7a174830 BombieriVinogradov/Proof/SiegelWalfisz/ExplicitFormula/Centered/UnitHalfSum.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Definitions
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Unit-point Chebyshev half-sum

This module evaluates the centering value of the half-weighted character
Chebyshev sum.
-/
set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The half-weighted character Chebyshev sum vanishes at one. -/
theorem characterChebyshevHalfSum_one
    {N : Nat} (chi : DirichletCharacter Complex N) :
    characterChebyshevHalfSum 1 chi = 0 := by
  simp [characterChebyshevHalfSum, twistedMangoldtSequence]

end BombieriVinogradov.SiegelWalfisz

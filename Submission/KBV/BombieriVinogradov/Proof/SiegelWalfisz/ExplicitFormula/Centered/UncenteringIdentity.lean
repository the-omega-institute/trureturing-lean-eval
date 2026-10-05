-- Vendored from kimihiro64/bombieri-vinogradov@7a174830 BombieriVinogradov/Proof/SiegelWalfisz/ExplicitFormula/Centered/UncenteringIdentity.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.ExceptionalResidueSum
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.ZeroSum
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Definitions
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.HalfSumBridge
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronSeries.Definitions
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic.Ring

/-!
# Exact uncentering of the explicit-formula residual

The half-weight endpoint and the x=1 zero sum are restored algebraically.
The origin term is an explicit arbitrary input, so its analytic formula
and estimate remain separate from this identity.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem uncenteredExplicitFormulaResidual_eq_centered
    {N x : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (hx : 0 < x) (T : Real) (exceptional : Option Complex)
    (origin : Complex) :
    characterChebyshevSum x chi +
        truncatedCriticalZeroSum chi x T exceptional +
        exceptionalZeroContribution x exceptional =
      (characterChebyshevHalfSum x chi + origin +
          centeredTruncatedCriticalZeroSum chi x T exceptional -
          centeredExceptionalResidueSum chi x exceptional) +
        (1 / 2 : Complex) * twistedMangoldtSequence chi x - origin +
        truncatedCriticalZeroSum chi 1 T exceptional +
        (centeredExceptionalResidueSum chi x exceptional +
          exceptionalZeroContribution x exceptional) := by
  rw [characterChebyshevHalfSum_eq_characterChebyshevSum_sub chi hx]
  unfold centeredTruncatedCriticalZeroSum
  ring

end BombieriVinogradov.SiegelWalfisz

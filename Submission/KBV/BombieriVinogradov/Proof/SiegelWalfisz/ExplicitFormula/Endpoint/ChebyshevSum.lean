-- Vendored from kimihiro64/bombieri-vinogradov@7a174830 BombieriVinogradov/Proof/SiegelWalfisz/ExplicitFormula/Endpoint/ChebyshevSum.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
import Submission.KBV.BombieriVinogradov.Definitions.VaughanMeanValue
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.Coefficient
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronSeries.Definitions
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Group.Defs
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic.NormNum

/-!
# The finite character Chebyshev sum at two

The summand at one vanishes; the remaining twisted Mangoldt coefficient
is bounded by log two uniformly in the character and its level.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_characterChebyshevSum_two_le_log_two
    {N : Nat} (chi : DirichletCharacter Complex N) :
    norm (characterChebyshevSum 2 chi) <= Real.log 2 := by
  have hValue : characterChebyshevSum 2 chi = twistedMangoldtSequence chi 2 := by
    norm_num [characterChebyshevSum,
      BombieriVinogradov.VaughanMeanValue.psiCharacterSum,
      twistedMangoldtSequence, Finset.sum_Icc_succ_top, mul_comm]
  rw [hValue]
  exact (norm_twistedMangoldtSequence_le_vonMangoldt chi 2).trans
    ArithmeticFunction.vonMangoldt_le_log

end BombieriVinogradov.SiegelWalfisz

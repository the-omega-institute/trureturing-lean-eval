-- Vendored from kimihiro64/bombieri-vinogradov@7a174830 BombieriVinogradov/Proof/SiegelWalfisz/ExplicitFormula/Imprimitive/ChebyshevCorrection.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
import Submission.KBV.BombieriVinogradov.Definitions.VaughanMeanValue
import Submission.KBV.BombieriVinogradov.Helpers.ArithmeticFunction.NonCoprimeMangoldtBound
import Submission.KBV.BombieriVinogradov.Helpers.DirichletCharacter.PrimitiveSumDifference
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Finite Euler correction of the character Chebyshev sum

Character agreement away from the ambient prime divisors and the complete
prime-power divisor bound give one absolute logarithmic correction.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_characterChebyshevSum_sub_primitive_le
    {N x : Nat} (hN : Ne N 0) (chi : _root_.DirichletCharacter Complex N)
    (hx : 0 < x) :
    norm (characterChebyshevSum x chi -
      characterChebyshevSum x chi.primitiveCharacter) <=
        Real.log N * Real.log x / Real.log (2 : Real) := by
  change norm (VaughanMeanValue.psiCharacterSum x N chi -
    VaughanMeanValue.psiCharacterSum x chi.conductor chi.primitiveCharacter) <= _
  exact (VaughanMeanValue.norm_psiCharacterSum_sub_primitive_le_mangoldt chi x).trans
    (nonCoprimeMangoldtSum_le_log_mul_log hN hx)

end BombieriVinogradov.SiegelWalfisz

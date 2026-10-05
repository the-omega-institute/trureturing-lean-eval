-- Vendored from kimihiro64/bombieri-vinogradov@7a174830 BombieriVinogradov/Proof/SiegelWalfisz/CharacterEstimate/ChebyshevCorrectionDecay.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
import Submission.KBV.BombieriVinogradov.Helpers.RealAnalysis.LogarithmicEulerDecay
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Imprimitive.ChebyshevCorrection
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Exponential decay of the finite Euler correction

The uniform logarithmic Euler mass estimate bounds the difference between
the ambient and primitive character Chebyshev sums at the selected scale.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_characterChebyshevSum_sub_primitive_le_exp
    {a : Real} (ha : a <= (1 / 2 : Real)) {N x : Nat} [NeZero N]
    (hN : 3 <= N) (chi : _root_.DirichletCharacter Complex N)
    (hx : 3 <= x)
    (hMod : (N : Real) <= Real.exp (Real.sqrt (Real.log x))) :
    norm (characterChebyshevSum x chi -
      characterChebyshevSum x chi.primitiveCharacter) <=
        (48 / Real.log (2 : Real)) *
          ((x : Real) * Real.exp (-(a * Real.sqrt (Real.log x)))) := by
  have hxPos : 0 < x := Nat.lt_of_lt_of_le (by decide : 0 < 3) hx
  exact (norm_characterChebyshevSum_sub_primitive_le (NeZero.ne N) chi hxPos).trans
    (BombieriVinogradov.RealAnalysis.logarithmicEulerMass_le_exp ha hN hx hMod)

end BombieriVinogradov.SiegelWalfisz

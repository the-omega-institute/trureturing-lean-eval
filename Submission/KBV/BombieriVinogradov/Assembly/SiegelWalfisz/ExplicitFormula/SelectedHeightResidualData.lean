-- Vendored from kimihiro64/bombieri-vinogradov@7a174830 BombieriVinogradov/Assembly/SiegelWalfisz/ExplicitFormula/SelectedHeightResidualData.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
import Submission.KBV.BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.SelectedHeightContourData
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Definitions
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Basic.Complex.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Selected-height residual data
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

structure SelectedHeightResidualData
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (x : Nat) (T CHeight CResidual : Real)
    (exceptional : Option Complex) where
  contour : SelectedHeightContourData chi x T CHeight exceptional
  residual_bound :
    norm
        (characterChebyshevHalfSum x chi +
          (lFunctionOriginMultiplicity chi : Complex) *
            Complex.log (x : Complex) +
          centeredTruncatedCriticalZeroSum chi x contour.height exceptional -
          centeredExceptionalResidueSum chi x exceptional) <=
      CResidual *
        ((x : Real) / T *
          (Real.log ((N * x : Nat) : Real)) ^ 2)

end BombieriVinogradov.SiegelWalfisz

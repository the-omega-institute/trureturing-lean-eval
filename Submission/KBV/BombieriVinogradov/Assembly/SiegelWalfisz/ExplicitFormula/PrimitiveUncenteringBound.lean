-- Vendored from kimihiro64/bombieri-vinogradov@7a174830 BombieriVinogradov/Assembly/SiegelWalfisz/ExplicitFormula/PrimitiveUncenteringBound.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
import Submission.KBV.BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.OptionalExceptionalCenteringBound
import Submission.KBV.BombieriVinogradov.Helpers.ComplexAnalysis.FiveTermNorm
import Submission.KBV.BombieriVinogradov.Helpers.RealAnalysis.UncenteringError
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.ExceptionalResidueSum
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.UncenteringIdentity
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.ZeroSum
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.ZeroFreeData
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Definitions
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.Definitions
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.SourceScale.Endpoint
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.SourceScale.Origin
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic.Positivity

/-!
# The fixed-parameter primitive uncentering estimate

Five separately proved corrections are absorbed at the published scale.
Uniform choices of the centered and retained-sum constants are made by
the outward assembler, not by this fixed-parameter estimate.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem primitiveExplicitFormula_le_of_centered_and_unit_bounds
    {N x : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hN : 3 <= N) (hchi : Ne chi 1)
    (hPrimitive : DirichletCharacter.IsPrimitive chi) (hx : 2 < x)
    {T c A B : Real} (hT : 2 <= T) (hTx : T <= x)
    (hA : 0 <= A) (hB : 0 <= B)
    (hData : ExplicitFormulaZeroFreeData c chi)
    (exceptional : Option Complex)
    (hChoice : IsExceptionalZeroChoice c chi exceptional)
    (hPrimary : 1 <= (x : Real) / T *
      (Real.log ((N * x : Nat) : Real)) ^ 2)
    (hCenteredBound : norm (characterChebyshevHalfSum x chi +
      (lFunctionOriginMultiplicity chi : Complex) * Complex.log (x : Complex) +
      centeredTruncatedCriticalZeroSum chi x T exceptional -
      centeredExceptionalResidueSum chi x exceptional) <=
        A * ((x : Real) / T * (Real.log ((N * x : Nat) : Real)) ^ 2))
    (hUnitBound : norm (truncatedCriticalZeroSum chi 1 T exceptional) <=
      B * ((x : Real) / T * (Real.log ((N * x : Nat) : Real)) ^ 2)) :
    norm (characterChebyshevSum x chi +
      truncatedCriticalZeroSum chi x T exceptional +
      exceptionalZeroContribution x exceptional) <=
      (A + B + 4) * explicitFormulaRemainderMajorant N x T := by
  rw [uncenteredExplicitFormulaResidual_eq_centered (x := x) chi (by omega) T
    exceptional ((lFunctionOriginMultiplicity chi : Complex) *
      Complex.log (x : Complex))]
  unfold explicitFormulaRemainderMajorant
  exact (BombieriVinogradov.ComplexAnalysis.norm_add_sub_add_add_le_of_le
    hCenteredBound
    (norm_half_mul_twistedMangoldtSequence_le_sourceScale chi hN hx hT hTx)
    (norm_originMultiplicity_mul_log_le_sourceScale hchi hPrimitive hN hx hT hTx)
    hUnitBound
    (norm_optionalExceptionalCenteringCorrection_le hchi hPrimitive hx
      hData exceptional hChoice)).trans
      (BombieriVinogradov.RealAnalysis.uncentering_error_le_uniform_scale
        hA hB hPrimary (by positivity))

end BombieriVinogradov.SiegelWalfisz

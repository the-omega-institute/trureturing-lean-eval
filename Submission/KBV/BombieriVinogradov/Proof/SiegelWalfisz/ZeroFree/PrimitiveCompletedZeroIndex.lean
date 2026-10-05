-- Vendored from kimihiro64/bombieri-vinogradov@7a174830 BombieriVinogradov/Proof/SiegelWalfisz/ZeroFree/PrimitiveCompletedZeroIndex.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
import Submission.KBV.BombieriVinogradov.Helpers.ComplexAnalysis.DivisorZeroIndex
import Submission.KBV.BombieriVinogradov.Helpers.DirichletCharacter.ConductorFacts
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedNormalization
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedOriginNonvanishing
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedProductFormula
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroIndex
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.ImprimitiveLFunctionZero
import Mathlib.Tactic.NormNum

/-!
# Packaging an ambient L-function zero as a primitive completed zero

This module transfers an open-right-half-plane zero through the inducing
primitive character and constructs its multiplicity-aware completed-function
divisor index without changing the zero's complex value.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_primitive_completedZeroIndex_of_LFunction_eq_zero
    {N : Nat} [NeZero N] (chi : _root_.DirichletCharacter Complex N)
    [NeZero chi.conductor]
    (hchi : chi ≠ 1) {s : Complex} (hs : 0 < s.re)
    (hzero : chi.LFunction s = 0) :
    exists p : SymmetricCompletedZeroIndex chi.primitiveCharacter,
      Complex.Hadamard.divisorZeroIndex₀_val p = s := by
  have hPrimitiveNe :=
    BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one
      chi hchi
  have hPrimitive := chi.primitiveCharacter_isPrimitive
  have hPrimitiveZero :=
    primitive_LFunction_eq_zero_of_LFunction_eq_zero chi hchi hs hzero
  have hCompleted :=
    BombieriVinogradov.SiegelWalfisz.DirichletCharacter.completedLFunction_eq_LFunction_mul_gammaFactor_of_re_pos
      chi.primitiveCharacter hs
  rw [hPrimitiveZero, zero_mul] at hCompleted
  have hSymmetric : symmetricCompletedLFunction chi.primitiveCharacter s = 0 := by
    rw [symmetricCompletedLFunction, hCompleted, mul_zero]
  have hsNe : s ≠ 0 := by
    intro hsZero
    rw [hsZero] at hs
    norm_num at hs
  have hEntire := differentiable_symmetricCompletedLFunction hPrimitiveNe
  have hNonzero : exists w : Complex,
      symmetricCompletedLFunction chi.primitiveCharacter w ≠ 0 :=
    Exists.intro 0
      (symmetricCompletedLFunction_zero_ne_zero hPrimitiveNe hPrimitive)
  exact BombieriVinogradov.exists_divisorZeroIndex₀_val_eq_of_apply_eq_zero
    hEntire hNonzero hsNe hSymmetric

end BombieriVinogradov.SiegelWalfisz

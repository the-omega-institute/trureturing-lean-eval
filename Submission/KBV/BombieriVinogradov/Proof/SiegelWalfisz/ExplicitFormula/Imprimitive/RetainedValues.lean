-- Vendored from kimihiro64/bombieri-vinogradov@7a174830 BombieriVinogradov/Proof/SiegelWalfisz/ExplicitFormula/Imprimitive/RetainedValues.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Imprimitive.Multiplicity
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Imprimitive.ValueTransport
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.RetainedZeroValues
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Equality of the ambient and primitive retained zero-value sets

Positive-half-plane multiplicity equality transports precisely the
strict-strip cutoff and the same optional excluded pair.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem retainedCriticalZeroValues_eq_primitive
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    [NeZero chi.conductor] (hchi : Ne chi 1)
    (T : Real) (exceptional : Option Complex) :
    retainedCriticalZeroValues chi T exceptional =
      retainedCriticalZeroValues chi.primitiveCharacter T exceptional := by
  exact retainedCriticalZeroValues_eq_of_completedMultiplicity_eq
    chi chi.primitiveCharacter
    (fun (s : Complex) hs => completedDivisorMultiplicity_eq_primitive chi hchi hs)
    T exceptional

end BombieriVinogradov.SiegelWalfisz

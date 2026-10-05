-- Vendored from kimihiro64/bombieri-vinogradov@7a174830 BombieriVinogradov/Proof/SiegelWalfisz/ZeroFree/CompletedZeroIndex.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedNormalization
import Submission.PNT.PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorIndex

/-!
# Multiplicity-aware zero index for a symmetric completed L-function

This module provides the narrow shared type alias used by zero-divisor consumers.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

abbrev SymmetricCompletedZeroIndex
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) :=
  Complex.Hadamard.divisorZeroIndex₀
    (symmetricCompletedLFunction chi) (Set.univ : Set Complex)

end BombieriVinogradov.SiegelWalfisz

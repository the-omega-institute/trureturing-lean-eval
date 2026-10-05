-- Vendored from kimihiro64/bombieri-vinogradov@7a174830 BombieriVinogradov/Proof/SiegelWalfisz/ExplicitFormula/Residue/Origin/Definitions.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Origin data for the explicit-formula integrand

This module owns only the L-function multiplicity at zero and the
logarithmic-derivative remainder after subtracting its principal part.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The analytic multiplicity of a Dirichlet L-function at zero. -/
def lFunctionOriginMultiplicity
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) : Nat :=
  analyticOrderNatAt chi.LFunction 0

/-- The logarithmic derivative after subtracting its origin principal
part. -/
def lFunctionOriginLogDerivativeRemainder
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (s : Complex) : Complex :=
  logDeriv chi.LFunction s - (lFunctionOriginMultiplicity chi : Complex) / s

end BombieriVinogradov.SiegelWalfisz

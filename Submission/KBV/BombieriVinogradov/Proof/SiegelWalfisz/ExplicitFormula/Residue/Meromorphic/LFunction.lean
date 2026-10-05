-- Vendored from kimihiro64/bombieri-vinogradov@7a174830 BombieriVinogradov/Proof/SiegelWalfisz/ExplicitFormula/Residue/Meromorphic/LFunction.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Meromorphic logarithmic derivative of a Dirichlet L-function

This module proves only the global meromorphicity of the logarithmic derivative
for a nonprincipal character.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The logarithmic derivative of a nonprincipal Dirichlet L-function is
meromorphic on the complex plane. -/
theorem meromorphic_logDeriv_LFunction
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) : Meromorphic (logDeriv chi.LFunction) := by
  apply Meromorphic.logDeriv
  intro s
  exact ((DirichletCharacter.differentiable_LFunction hchi).analyticAt s).meromorphicAt

end BombieriVinogradov.SiegelWalfisz

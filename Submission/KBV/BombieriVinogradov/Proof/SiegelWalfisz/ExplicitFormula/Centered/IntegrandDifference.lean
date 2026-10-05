-- Vendored from kimihiro64/bombieri-vinogradov@7a174830 BombieriVinogradov/Proof/SiegelWalfisz/ExplicitFormula/Centered/IntegrandDifference.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Integrand
import Mathlib.Tactic.Ring

/-!
# Centered explicit-formula integrand identity

This module isolates the algebraic normalization of the difference between
the x-integrand and the unit integrand.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz
theorem explicitFormulaIntegrand_sub_one_eq
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (x : Nat) (s : Complex) :
    explicitFormulaIntegrand chi x s -
        explicitFormulaIntegrand chi 1 s =
      logDeriv chi.LFunction s *
        (-(((x : Complex) ^ s - 1) / s)) := by
  simp [explicitFormulaIntegrand]
  ring

end BombieriVinogradov.SiegelWalfisz

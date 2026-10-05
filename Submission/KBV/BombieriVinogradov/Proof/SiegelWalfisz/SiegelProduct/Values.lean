-- Vendored from kimihiro64/bombieri-vinogradov@7a174830 BombieriVinogradov/Proof/SiegelWalfisz/SiegelProduct/Values.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Quadratic character values

This module isolates the three-value classification used in the local Euler-factor analysis.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

/-- A quadratic complex Dirichlet character takes only the values zero, one, and minus one. -/
theorem quadraticValue_cases {N : ℕ} (χ : DirichletCharacter ℂ N)
    (hχ : χ ^ 2 = 1) (n : ℕ) :
    χ n = 0 ∨ χ n = 1 ∨ χ n = -1 :=
  MulChar.isQuadratic_iff_sq_eq_one.mpr hχ n

end BombieriVinogradov.SiegelWalfisz

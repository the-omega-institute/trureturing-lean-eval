-- Vendored from kimihiro64/bombieri-vinogradov@7a174830 BombieriVinogradov/Proof/SiegelWalfisz/ExplicitFormula/Horizontal/ZeroHeightScale.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Shared logarithmic scale for horizontal contour heights

This module owns the modulus-height logarithmic scale reused by good-height
selection and the later top and bottom contour estimates.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

/-- A positive-buffered modulus-height logarithmic scale. -/
noncomputable def zeroHeightLogScale (N : Nat) (T : Real) : Real :=
  Real.log N + Real.log (T + 3) + 1

end BombieriVinogradov.SiegelWalfisz

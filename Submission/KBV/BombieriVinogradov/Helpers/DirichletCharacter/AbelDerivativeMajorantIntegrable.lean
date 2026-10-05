-- Vendored from kimihiro64/bombieri-vinogradov@7a174830 BombieriVinogradov/Helpers/DirichletCharacter/AbelDerivativeMajorantIntegrable.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
import Submission.KBV.BombieriVinogradov.Helpers.DirichletCharacter.LogRpowIntegrable

/-!
# Integrability of the character Abel derivative majorant

This module owns multiplication of the logarithmic-power tail majorant by the
character modulus.
-/

set_option autoImplicit false

open MeasureTheory Set

namespace BombieriVinogradov

/-- The modulus-scaled derivative majorant is integrable on `(1, infinity)`. -/
theorem integrableOn_characterAbelDerivativeMajorant {N : Nat} {s0 : Complex}
    (hs0 : 0 < s0.re) :
    IntegrableOn
      (fun t : Real => (N : Real) * (Real.log t * t ^ (-(s0.re / 2 + 1)))) (Ioi 1) := by
  exact (integrableOn_log_mul_rpow_neg_add_one (half_pos hs0)).const_mul (N : Real)

end BombieriVinogradov

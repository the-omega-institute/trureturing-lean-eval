-- Vendored from kimihiro64/bombieri-vinogradov@7a174830 BombieriVinogradov/Proof/SiegelWalfisz/ExplicitFormula/Residue/Origin/CorrectionRectangleIntegral.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
import Submission.KBV.BombieriVinogradov.Helpers.ComplexAnalysis.RectangleInverseSquare
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.RegularizedDefinitions

/-!
# Rectangle integral of the origin correction

This module specializes the reusable inverse-square contour identity to the
character-dependent correction used by the explicit-formula integrand.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The origin double-pole correction has zero normalized rectangle integral
when the rectangle border avoids zero. -/
theorem rectangleIntegral'_originDoublePoleCorrection_eq_zero
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (z w : Complex)
    (hzero : Not (Membership.mem (RectangleBorder z w) 0)) :
    RectangleIntegral' (originDoublePoleCorrection chi) z w = 0 := by
  change RectangleIntegral'
    (fun s : Complex => (lFunctionOriginMultiplicity chi : Complex) / s ^ 2)
    z w = 0
  exact
    BombieriVinogradov.ComplexAnalysis.rectangleIntegral'_div_sq_eq_zero
      (lFunctionOriginMultiplicity chi : Complex) z w hzero

end BombieriVinogradov.SiegelWalfisz

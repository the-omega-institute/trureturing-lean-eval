-- Vendored from kimihiro64/bombieri-vinogradov@7a174830 BombieriVinogradov/Proof/SiegelWalfisz/ExplicitFormula/Residue/Origin/RegularizedMeromorphic.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Meromorphic.Main
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.RegularizedDefinitions

/-!
# Meromorphicity of the origin-regularized integrand

This module proves only global meromorphicity of the correction and corrected
integrand.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The origin double-pole correction is meromorphic. -/
theorem meromorphic_originDoublePoleCorrection
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) :
    Meromorphic (originDoublePoleCorrection chi) := by
  intro s
  unfold originDoublePoleCorrection
  exact (MeromorphicAt.const
    (lFunctionOriginMultiplicity chi : Complex) s).div (by fun_prop)

/-- The double-pole-corrected explicit-formula integrand is meromorphic. -/
theorem meromorphic_regularizedExplicitFormulaIntegrand
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (x : Nat) (hx : 0 < x) :
    Meromorphic (regularizedExplicitFormulaIntegrand chi x) := by
  exact (meromorphic_explicitFormulaIntegrand hchi x hx).add
    (meromorphic_originDoublePoleCorrection chi)

end BombieriVinogradov.SiegelWalfisz

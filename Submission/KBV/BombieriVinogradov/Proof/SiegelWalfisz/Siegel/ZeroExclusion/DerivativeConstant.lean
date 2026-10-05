-- Vendored from kimihiro64/bombieri-vinogradov@7a174830 BombieriVinogradov/Proof/SiegelWalfisz/Siegel/ZeroExclusion/DerivativeConstant.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.Siegel.ZeroExclusion.ValueConstant

/-!
# Absolute constant in the near-one derivative bound

This module only packages the Cauchy-radius factor with the value-bound
constant.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def characterLDerivativeBoundConstant : ℝ :=
  16 * characterLNearOneBoundConstant

theorem characterLDerivativeBoundConstant_pos :
    0 < characterLDerivativeBoundConstant := by
  unfold characterLDerivativeBoundConstant
  exact mul_pos (by norm_num) characterLNearOneBoundConstant_pos

end BombieriVinogradov.SiegelWalfisz

-- Vendored from kimihiro64/bombieri-vinogradov@7a174830 BombieriVinogradov/Proof/SiegelWalfisz/ExplicitFormula/SourceScale/ZeroHeight.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Horizontal.ZeroHeightScale
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.SourceScale.Basic
import Mathlib.Tactic.Linarith

/-!
# Zero-height scale versus the source logarithm
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem zeroHeightLogScale_le_three_mul_sourceLog
    {N x : Nat} (hN : 3 <= N) (hx : 2 < x)
    {T : Real} (hT : 2 <= T) (hTx : T <= x) :
    zeroHeightLogScale N T <=
      3 * Real.log ((N * x : Nat) : Real) := by
  have hLogN :=
    log_level_le_log_level_mul_argument hN hx
  have hLogT :=
    log_height_add_three_le_log_level_mul_argument hN hx hT hTx
  have hLogOne :=
    one_le_log_level_mul_argument hN hx
  unfold zeroHeightLogScale
  linarith

end BombieriVinogradov.SiegelWalfisz

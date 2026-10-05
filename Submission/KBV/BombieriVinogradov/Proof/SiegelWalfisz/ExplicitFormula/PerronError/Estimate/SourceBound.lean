-- Vendored from kimihiro64/bombieri-vinogradov@7a174830 BombieriVinogradov/Proof/SiegelWalfisz/ExplicitFormula/PerronError/Estimate/SourceBound.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.Coefficient
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.SourceSummable
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Main

/-!
# Source form of the Perron error bound

This module replaces the character-dependent coefficient norms by the source
von Mangoldt weights in the complete Lemma 13.4 bound.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The finite explicit-formula integral differs from the half-weighted
character Chebyshev sum by at most the source von Mangoldt Perron series. -/
theorem norm_explicitFormulaVerticalIntegral_sub_halfSum_le_source
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    {x : Nat} (hx : 0 < x) {c T : Real} (hc : 1 < c) (hT : 0 < T) :
    norm (explicitFormulaVerticalIntegral chi x c T -
      characterChebyshevHalfSum x chi) <=
      tsum (sourcePerronErrorMajorantTerm x c T) := by
  exact (norm_explicitFormulaVerticalIntegral_sub_halfSum_le chi hx hc hT).trans
    ((summable_scalarPerronErrorMajorantTerm chi hx hc hT).tsum_le_tsum
      (fun n => scalarPerronErrorMajorantTerm_le_source chi hx
        (lt_trans zero_lt_one hc) hT n)
      (summable_sourcePerronErrorMajorantTerm hx hc hT))

end BombieriVinogradov.SiegelWalfisz

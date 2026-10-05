-- Vendored from kimihiro64/bombieri-vinogradov@7a174830 BombieriVinogradov/Proof/SiegelWalfisz/ExplicitFormula/Centered/BoundaryDecomposition.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.BottomBoundaryIntegral
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.BrokenBoundaryIntegral
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.LeftBoundaryIntegral
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.TopBoundaryIntegral
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic.Ring

/-!
# Centered broken-boundary decomposition

This module reassembles the separately owned bottom, left, and top centered
contour segments.
-/
set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The centered broken boundary is the sum of its three centered segments. -/
theorem centeredBrokenBoundaryIntegral_eq_segments
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (x : Nat) (U c T : Real) :
    centeredExplicitFormulaBrokenBoundaryIntegral chi x U c T =
      centeredExplicitFormulaBottomBoundaryIntegral chi x U c T +
        centeredExplicitFormulaLeftBoundaryIntegral chi x U T +
          centeredExplicitFormulaTopBoundaryIntegral chi x U c T := by
  unfold centeredExplicitFormulaBrokenBoundaryIntegral
  unfold explicitFormulaBrokenBoundaryIntegral
  unfold centeredExplicitFormulaBottomBoundaryIntegral
  unfold centeredExplicitFormulaLeftBoundaryIntegral
  unfold centeredExplicitFormulaTopBoundaryIntegral
  ring

end BombieriVinogradov.SiegelWalfisz

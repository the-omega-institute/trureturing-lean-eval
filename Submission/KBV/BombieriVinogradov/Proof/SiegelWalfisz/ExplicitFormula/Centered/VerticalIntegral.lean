-- Vendored from kimihiro64/bombieri-vinogradov@7a174830 BombieriVinogradov/Proof/SiegelWalfisz/ExplicitFormula/Centered/VerticalIntegral.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronSeries.Definitions
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Centered explicit-formula vertical integral

This module centers the finite vertical integral at x equals one while keeping
the same vertical line and truncation height.
-/
set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The centered vertical integral is its x-value minus its value at one. -/
def centeredExplicitFormulaVerticalIntegral
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (x : Nat) (c T : Real) : Complex :=
  explicitFormulaVerticalIntegral chi x c T -
    explicitFormulaVerticalIntegral chi 1 c T

/-- Centering makes the vertical integral vanish at one. -/
theorem centeredExplicitFormulaVerticalIntegral_one
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (c T : Real) :
    centeredExplicitFormulaVerticalIntegral chi 1 c T = 0 := by
  simp [centeredExplicitFormulaVerticalIntegral]

end BombieriVinogradov.SiegelWalfisz

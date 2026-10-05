-- Vendored from kimihiro64/bombieri-vinogradov@7a174830 BombieriVinogradov/Proof/SiegelWalfisz/ExplicitFormula/Centered/LeftBoundaryIntegral.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Integrand
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Submission.PNT.PrimeNumberTheoremAnd.ResidueCalcOnRectangles

/-!
# Centered left contour integral

This module isolates the left vertical segment of the centered contour.
-/
set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- Difference of the left vertical integrals at x and at one. -/
def centeredExplicitFormulaLeftBoundaryIntegral
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (x : Nat) (U T : Real) : Complex :=
  VIntegral' (explicitFormulaIntegrand chi x) (-U) (-T) T -
    VIntegral' (explicitFormulaIntegrand chi 1) (-U) (-T) T

/-- The centered left integral vanishes at one. -/
theorem centeredExplicitFormulaLeftBoundaryIntegral_one
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (U T : Real) :
    centeredExplicitFormulaLeftBoundaryIntegral chi 1 U T = 0 := by
  simp [centeredExplicitFormulaLeftBoundaryIntegral]

end BombieriVinogradov.SiegelWalfisz

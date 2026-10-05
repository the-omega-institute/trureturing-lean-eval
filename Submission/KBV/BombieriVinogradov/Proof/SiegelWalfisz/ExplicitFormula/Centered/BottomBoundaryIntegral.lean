-- Vendored from kimihiro64/bombieri-vinogradov@7a174830 BombieriVinogradov/Proof/SiegelWalfisz/ExplicitFormula/Centered/BottomBoundaryIntegral.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Integrand
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Submission.PNT.PrimeNumberTheoremAnd.ResidueCalcOnRectangles

/-!
# Centered bottom contour integral

This module isolates the bottom horizontal segment of the centered contour.
-/
set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- Difference of the bottom horizontal integrals at x and at one. -/
def centeredExplicitFormulaBottomBoundaryIntegral
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (x : Nat) (U c T : Real) : Complex :=
  HIntegral' (explicitFormulaIntegrand chi x) c (-U) (-T) -
    HIntegral' (explicitFormulaIntegrand chi 1) c (-U) (-T)

/-- The centered bottom integral vanishes at one. -/
theorem centeredExplicitFormulaBottomBoundaryIntegral_one
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (U c T : Real) :
    centeredExplicitFormulaBottomBoundaryIntegral chi 1 U c T = 0 := by
  simp [centeredExplicitFormulaBottomBoundaryIntegral]

end BombieriVinogradov.SiegelWalfisz

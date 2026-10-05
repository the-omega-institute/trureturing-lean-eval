-- Vendored from kimihiro64/bombieri-vinogradov@7a174830 BombieriVinogradov/Proof/SiegelWalfisz/ExplicitFormula/Centered/ResidueDecomposition.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.ContourResidueSum
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.ExceptionalResidueSum
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.ZeroSum
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Contour.Definitions
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.Definitions
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.RegularizedDefinitions
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.RegularizedResidueDecomposition
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Set.Lattice.Bounded
import Mathlib.Data.Set.Lattice.Disjoint
import Mathlib.Data.Set.Lattice.Image
import Mathlib.Data.Set.Lattice.Indexed
import Mathlib.Data.Set.Lattice.Order
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Submission.PNT.PrimeNumberTheoremAnd.Rectangle
import Submission.PNT.PrimeNumberTheoremAnd.ResidueCalcOnRectangles

/-!
# Centered contour residue decomposition

This module subtracts the x equals one residue identity from the x identity.
The finite origin logarithmic-derivative value cancels exactly.
-/
set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The centered contour residue sum contains only the origin multiplicity
logarithm and the centered retained and exceptional zero contributions. -/
theorem centeredRegularizedContourResidueSum_eq_decomposed
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (x : Nat) (hx : 0 < x) (c0 U c T : Real)
    (hUNonneg : 0 <= U) (hULt : U < 1) (hc : 1 <= c) (hT : 0 < T)
    (exceptional : Option Complex)
    (hChoice : IsExceptionalZeroChoice c0 chi exceptional)
    (horiginalX : Disjoint
      (RectangleBorder (explicitFormulaContourLowerLeft U T)
        (explicitFormulaContourUpperRight c T))
      {rho | meromorphicOrderAt (explicitFormulaIntegrand chi x) rho < 0})
    (horiginalOne : Disjoint
      (RectangleBorder (explicitFormulaContourLowerLeft U T)
        (explicitFormulaContourUpperRight c T))
      {rho | meromorphicOrderAt (explicitFormulaIntegrand chi 1) rho < 0})
    (hzero : Not ((RectangleBorder (explicitFormulaContourLowerLeft U T)
      (explicitFormulaContourUpperRight c T)) 0)) :
    centeredRegularizedContourResidueSum chi x U c T =
      -(lFunctionOriginMultiplicity chi : Complex) *
          Complex.log (x : Complex) +
        (-centeredTruncatedCriticalZeroSum chi x T exceptional +
          centeredExceptionalResidueSum chi x exceptional) := by
  unfold centeredRegularizedContourResidueSum
  rw [sumResiduesIn_regularizedContour_eq_decomposed
    hchi hPrimitive x hx c0 U c T hUNonneg hULt hc hT exceptional
    hChoice horiginalX hzero]
  rw [sumResiduesIn_regularizedContour_eq_decomposed
    hchi hPrimitive 1 (by norm_num) c0 U c T hUNonneg hULt hc hT exceptional
    hChoice horiginalOne hzero]
  unfold centeredTruncatedCriticalZeroSum centeredExceptionalResidueSum
  simp
  ring

end BombieriVinogradov.SiegelWalfisz

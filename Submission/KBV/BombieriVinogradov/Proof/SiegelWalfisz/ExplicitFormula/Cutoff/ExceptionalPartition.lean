-- Vendored from kimihiro64/bombieri-vinogradov@7a174830 BombieriVinogradov/Proof/SiegelWalfisz/ExplicitFormula/Cutoff/ExceptionalPartition.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Cutoff.ExceptionalValuePartition
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.ZeroFacts
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.ZeroFreeData
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.ExceptionalZeroValues
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.ExceptionalResidueSum
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.RegularizedCriticalZeroSum
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.RegularizedDefinitions
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.RetainedExceptionalDisjoint
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.RetainedZeroValues
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic.Ring
import Submission.PNT.PrimeNumberTheoremAnd.ResidueCalcOnRectangles

/-!
# Exact change of the zero sum after excluding the exceptional pair

Residues retain analytic multiplicities. Simplicity of the selected zero
and its quadratic reflection evaluates the two excluded contributions.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem truncatedCriticalZeroSum_none_eq_exceptionalPartition
    {N x : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hx : 0 < x) {c : Real} (hData : ExplicitFormulaZeroFreeData c chi)
    {beta : Complex} (hExceptional : IsExceptionalZero c chi beta)
    {T : Real} (hT : 0 < T) :
    truncatedCriticalZeroSum chi x T none =
      truncatedCriticalZeroSum chi x T (some beta) +
        (x : Complex) ^ beta / beta +
        (x : Complex) ^ (1 - beta) / (1 - beta) := by
  have hValues := unexcludedCriticalZeroValues_eq_exceptionalPartition
    hchi hPrimitive hData hExceptional hT
  have hDisjoint := disjoint_retainedCriticalZeroValues_exceptionalZeroValues
    chi T (some beta)
  have hSums :
      Finset.sum (retainedCriticalZeroValues chi T none)
          (fun rho => residue (regularizedExplicitFormulaIntegrand chi x) rho) =
        Finset.sum (retainedCriticalZeroValues chi T (some beta))
          (fun rho => residue (regularizedExplicitFormulaIntegrand chi x) rho) +
        Finset.sum (exceptionalZeroValues (some beta))
          (fun rho => residue (regularizedExplicitFormulaIntegrand chi x) rho) := by
    rw [hValues, Finset.sum_union hDisjoint]
  have hFacts := hData.exceptional beta hExceptional
  rw [sum_residue_regularizedExplicitFormulaIntegrand_retainedCriticalZeroValues
      hchi hx T none,
    sum_residue_regularizedExplicitFormulaIntegrand_retainedCriticalZeroValues
      hchi hx T (some beta),
    sum_residue_regularizedExplicitFormulaIntegrand_exceptionalZeroValues_some
      hchi hPrimitive hFacts.quadratic hx hExceptional
        hFacts.simple hFacts.reflection_ne] at hSums
  calc
    truncatedCriticalZeroSum chi x T none =
        -(-truncatedCriticalZeroSum chi x T none) := (neg_neg _).symm
    _ = -(-truncatedCriticalZeroSum chi x T (some beta) +
        (-((x : Complex) ^ beta / beta) +
          -((x : Complex) ^ (1 - beta) / (1 - beta)))) := by
      rw [hSums]
    _ = truncatedCriticalZeroSum chi x T (some beta) +
        (x : Complex) ^ beta / beta +
        (x : Complex) ^ (1 - beta) / (1 - beta) := by
      ring

end BombieriVinogradov.SiegelWalfisz

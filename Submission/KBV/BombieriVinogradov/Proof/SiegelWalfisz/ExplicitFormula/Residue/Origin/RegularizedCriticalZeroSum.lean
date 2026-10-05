-- Vendored from kimihiro64/bombieri-vinogradov@7a174830 BombieriVinogradov/Proof/SiegelWalfisz/ExplicitFormula/Residue/Origin/RegularizedCriticalZeroSum.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.CriticalZeroResidueSum
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.RegularizedResidueAwayZero
import Submission.PNT.PrimeNumberTheoremAnd.ResidueCalcOnRectangles

/-!
# Regularized critical-zero residue sum

This module transfers the compiled multiplicity-aware retained-zero sum to
the origin-regularized integrand.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The retained critical-zero residues of the regularized integrand sum to
the negative truncated critical-zero contribution. -/
theorem sum_residue_regularizedExplicitFormulaIntegrand_retainedCriticalZeroValues
    {N x : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hx : 0 < x) (T : Real)
    (exceptional : Option Complex) :
    Finset.sum (retainedCriticalZeroValues chi T exceptional)
        (fun rho => residue (regularizedExplicitFormulaIntegrand chi x) rho) =
      -truncatedCriticalZeroSum chi x T exceptional := by
  calc
    Finset.sum (retainedCriticalZeroValues chi T exceptional)
        (fun rho => residue (regularizedExplicitFormulaIntegrand chi x) rho) =
        Finset.sum (retainedCriticalZeroValues chi T exceptional)
          (fun rho => residue (explicitFormulaIntegrand chi x) rho) := by
      apply Finset.sum_congr rfl
      intro rho hrho
      exact residue_regularizedExplicitFormulaIntegrand_eq_of_ne_zero
        hchi x hx (ne_zero_of_mem_retainedCriticalZeroValues hrho)
    _ = -truncatedCriticalZeroSum chi x T exceptional := by
      simpa only using
        sum_residue_explicitFormulaIntegrand_retainedCriticalZeroValues
          hchi hx T exceptional

end BombieriVinogradov.SiegelWalfisz

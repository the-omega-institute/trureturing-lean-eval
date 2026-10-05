-- Vendored from kimihiro64/bombieri-vinogradov@7a174830 BombieriVinogradov/Proof/SiegelWalfisz/ExplicitFormula/Cutoff/UnexcludedValueMembership.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.CriticalStripZeroValues
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.RetainedZeroValues
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroIndex
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroValue
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Set.Defs
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Ordinary zeros in the unexcluded finite value set

The primitive completed-index witness preserves the exact L-function zero
and its strict height cutoff.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem mem_unexcludedCriticalZeroValues_of_LFunction_eq_zero
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {rho : Complex} (hPos : 0 < rho.re) (hLt : rho.re < 1)
    {T : Real} (hHeight : abs rho.im < T) (hZero : chi.LFunction rho = 0) :
    (retainedCriticalZeroValues chi T none : Set Complex) rho := by
  classical
  have hWitness := exists_mem_criticalStripZeroTruncation_of_LFunction_eq_zero
    hchi hPrimitive hPos hLt hHeight hZero
  let p : SymmetricCompletedZeroIndex chi := hWitness.choose
  have hp : (criticalStripZeroTruncation chi T :
      Set (SymmetricCompletedZeroIndex chi)) p := hWitness.choose_spec.1
  have hValue : symmetricCompletedZeroValue p = rho := hWitness.choose_spec.2
  have hpNone : (retainedCriticalZeroIndices chi T none :
      Set (SymmetricCompletedZeroIndex chi)) p :=
    mem_retainedCriticalZeroIndices_iff.mpr (And.intro hp True.intro)
  exact Finset.mem_image.mpr (Exists.intro p (And.intro hpNone hValue))

end BombieriVinogradov.SiegelWalfisz

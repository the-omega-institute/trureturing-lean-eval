-- Vendored from kimihiro64/bombieri-vinogradov@7a174830 BombieriVinogradov/Proof/SiegelWalfisz/ExplicitFormula/Cutoff/ValuePartition.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Cutoff.RetainedValueMembership
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.ExceptionalZeroValues
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.RetainedZeroValues
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Set.Defs
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Partition of the unexcluded critical-zero values

When the exceptional pair occurs in the truncation, retained values and
that pair exhaust the unexcluded finite value set.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem unexcludedCriticalZeroValues_eq_retained_union_exceptional
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (T : Real) (e : Option Complex)
    (hIncluded : forall rho : Complex, (exceptionalZeroValues e : Set Complex) rho ->
      (retainedCriticalZeroValues chi T none : Set Complex) rho) :
    retainedCriticalZeroValues chi T none =
      Union.union (retainedCriticalZeroValues chi T e) (exceptionalZeroValues e) := by
  classical
  apply Finset.ext
  intro rho
  rw [Finset.mem_union]
  have hMembership := mem_retainedCriticalZeroValues_iff_unexcluded_and_retained
    chi T e rho
  exact Iff.intro
    (fun hNone => by
      by_cases hKept : IsRetainedZero e rho
      case pos => exact Or.inl (hMembership.mpr (And.intro hNone hKept))
      case neg => exact Or.inr (mem_exceptionalZeroValues_iff.mpr hKept))
    (fun hUnion => Or.elim hUnion
      (fun h => (hMembership.mp h).1)
      (fun h => hIncluded rho h))

end BombieriVinogradov.SiegelWalfisz

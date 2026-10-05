-- Vendored from kimihiro64/bombieri-vinogradov@7a174830 BombieriVinogradov/Proof/SiegelWalfisz/ExplicitFormula/Cutoff/ExceptionalValuePartition.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Cutoff.ExceptionalValues
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Cutoff.ValuePartition
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.ZeroFreeData
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.ExceptionalZeroValues
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.RetainedZeroValues
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Set.Defs
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# The exceptional pair partitions the primitive zero values

The actual selected pair supplies the inclusion hypothesis of the finite
value partition.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem unexcludedCriticalZeroValues_eq_exceptionalPartition
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {c : Real} (hData : ExplicitFormulaZeroFreeData c chi)
    {beta : Complex} (hExceptional : IsExceptionalZero c chi beta)
    {T : Real} (hT : 0 < T) :
    retainedCriticalZeroValues chi T none =
      Union.union (retainedCriticalZeroValues chi T (some beta))
        (exceptionalZeroValues (some beta)) := by
  have hPair := exceptionalPair_mem_unexcludedCriticalZeroValues
    hchi hPrimitive hData hExceptional hT
  apply unexcludedCriticalZeroValues_eq_retained_union_exceptional chi T (some beta)
  intro rho hrho
  have hCases : Or (rho = beta) (rho = 1 - beta) := by
    exact Or.elim (Finset.mem_insert.mp hrho)
      Or.inl (fun hs => Or.inr (Finset.mem_singleton.mp hs))
  exact Or.elim hCases
    (fun hEq => by rw [hEq]; exact hPair.1)
    (fun hEq => by
      rw [hEq]
      exact hPair.2)

end BombieriVinogradov.SiegelWalfisz

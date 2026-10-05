-- Vendored from kimihiro64/bombieri-vinogradov@7a174830 BombieriVinogradov/Proof/SiegelWalfisz/ExplicitFormula/Cutoff/RetainedZeroBand.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.RetainedZeroValues
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroIndex
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroValue
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Filter
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Set.Defs
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Absolute-ordinate bands of retained zeros
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

def retainedCriticalZeroBand
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (T : Real) (exceptional : Option Complex) (k : Nat) :
    Finset (SymmetricCompletedZeroIndex chi) := by
  classical
  exact (retainedCriticalZeroIndices chi T exceptional).filter fun p =>
    And ((k : Real) <= abs (symmetricCompletedZeroValue p).im)
      (abs (symmetricCompletedZeroValue p).im <
        ((k + 1 : Nat) : Real))

@[simp] theorem mem_retainedCriticalZeroBand_iff
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    {T : Real} {exceptional : Option Complex} {k : Nat}
    {p : SymmetricCompletedZeroIndex chi} :
    (retainedCriticalZeroBand chi T exceptional k :
      Set (SymmetricCompletedZeroIndex chi)) p <->
      And
        ((retainedCriticalZeroIndices chi T exceptional :
          Set (SymmetricCompletedZeroIndex chi)) p)
        (And ((k : Real) <= abs (symmetricCompletedZeroValue p).im)
          (abs (symmetricCompletedZeroValue p).im <
            ((k + 1 : Nat) : Real))) := by
  classical
  unfold retainedCriticalZeroBand
  have hForward :
      ((retainedCriticalZeroIndices chi T exceptional).filter
        (fun q => And ((k : Real) <=
          abs (symmetricCompletedZeroValue q).im)
          (abs (symmetricCompletedZeroValue q).im <
            ((k + 1 : Nat) : Real))) :
        Set (SymmetricCompletedZeroIndex chi)) p ->
      And
        ((retainedCriticalZeroIndices chi T exceptional :
          Set (SymmetricCompletedZeroIndex chi)) p)
        (And ((k : Real) <= abs (symmetricCompletedZeroValue p).im)
          (abs (symmetricCompletedZeroValue p).im <
            ((k + 1 : Nat) : Real))) :=
    fun hp => Finset.mem_filter.mp hp
  have hBackward :
      And
        ((retainedCriticalZeroIndices chi T exceptional :
          Set (SymmetricCompletedZeroIndex chi)) p)
        (And ((k : Real) <= abs (symmetricCompletedZeroValue p).im)
          (abs (symmetricCompletedZeroValue p).im <
            ((k + 1 : Nat) : Real))) ->
      ((retainedCriticalZeroIndices chi T exceptional).filter
        (fun q => And ((k : Real) <=
          abs (symmetricCompletedZeroValue q).im)
          (abs (symmetricCompletedZeroValue q).im <
            ((k + 1 : Nat) : Real))) :
        Set (SymmetricCompletedZeroIndex chi)) p :=
    fun hp => Finset.mem_filter.mpr hp
  exact Iff.intro hForward hBackward

end BombieriVinogradov.SiegelWalfisz

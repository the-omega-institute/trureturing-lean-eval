-- Vendored from kimihiro64/bombieri-vinogradov@7a174830 BombieriVinogradov/Helpers/DirichletCharacter/PrincipalMangoldtBound.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
import Submission.KBV.BombieriVinogradov.Definitions.VaughanMeanValue
import Submission.KBV.BombieriVinogradov.Definitions.WeightedBombieriVinogradov
import Submission.KBV.BombieriVinogradov.Helpers.ArithmeticFunction.NonCoprimeMangoldtBound
import Submission.KBV.BombieriVinogradov.Helpers.ComplexAnalysis.WeightedMangoldtCast
import Submission.KBV.BombieriVinogradov.Helpers.DirichletCharacter.PrincipalSumDifference
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat

/-!
# Logarithmic correction for the principal Mangoldt twist

The missing Euler factors contribute only the von Mangoldt mass
at indices not coprime to the modulus. The global center is unchanged.
-/
set_option autoImplicit false

namespace BombieriVinogradov.DirichletCharacter

theorem norm_psiGlobal_sub_principal_le_log_mul_log
    {N x : Nat} [NeZero N] (hx : 0 < x) :
    norm ((WeightedBombieriVinogradov.psiGlobal x : Complex) -
      VaughanMeanValue.psiCharacterSum x N (1 : _root_.DirichletCharacter Complex N)) <=
        Real.log N * Real.log x / Real.log (2 : Real) := by
  rw [WeightedBombieriVinogradov.ofReal_psiGlobal, VaughanMeanValue.psiCharacterSum,
    sum_sub_principal_eq_sum_filter, <- Complex.ofReal_sum]
  rw [Complex.norm_of_nonneg
    (Finset.sum_nonneg (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg))]
  exact nonCoprimeMangoldtSum_le_log_mul_log (NeZero.ne N) hx

end BombieriVinogradov.DirichletCharacter

-- Vendored from kimihiro64/bombieri-vinogradov@7a174830 BombieriVinogradov/Proof/SiegelWalfisz/ExplicitFormula/Residue/Origin/OddNonvanishing.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedNormalization
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedOriginNonvanishing
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Basic.Complex.Basic
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Tactic.NormNum

/-!
# Odd L-function nonvanishing at the origin
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem LFunction_zero_ne_zero_of_odd
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hOdd : DirichletCharacter.Odd chi) :
    Ne (chi.LFunction 0) 0 := by
  have hNNeOne : Ne N 1 := by
    intro hN
    exact hchi (chi.level_one' hN)
  have hCompletedNe : Ne (chi.completedLFunction 0) 0 := by
    have hSymmetric :=
      symmetricCompletedLFunction_zero_ne_zero hchi hPrimitive
    simpa [symmetricCompletedLFunction] using hSymmetric
  have hGammaPowerNe :
      Ne ((Real.pi : Complex) ^
        (-((0 : Complex) + 1) / 2)) 0 :=
    Complex.cpow_ne_zero_iff.mpr
      (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hGammaValueNe :
      Ne (Complex.Gamma (((0 : Complex) + 1) / 2)) 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by norm_num)
  have hGammaNe : Ne (chi.gammaFactor 0) 0 := by
    rw [DirichletCharacter.gammaFactor, ite_eq_right hOdd.not_even]
    change Ne
      ((Real.pi : Complex) ^ (-((0 : Complex) + 1) / 2) *
        Complex.Gamma (((0 : Complex) + 1) / 2)) 0
    exact mul_ne_zero hGammaPowerNe hGammaValueNe
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor
    chi 0 (Or.inr hNNeOne)]
  exact div_ne_zero hCompletedNe hGammaNe

end BombieriVinogradov.SiegelWalfisz

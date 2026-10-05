-- Vendored from kimihiro64/bombieri-vinogradov@7a174830 BombieriVinogradov/Proof/SiegelWalfisz/ExplicitFormula/Imprimitive/ExceptionalPredicate.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
import Submission.KBV.BombieriVinogradov.Helpers.DirichletCharacter.ConductorFacts
import Submission.KBV.BombieriVinogradov.Helpers.RealAnalysis.LogarithmicThreshold
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.ImprimitiveLFunctionZero
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Tactic.Linarith

/-!
# Exceptional zeros pass to the primitive character

The original level has a narrower logarithmic window than the conductor.
Right-half-plane nonvanishing of the finite Euler product transfers its zero.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem isExceptionalZero_primitive_of_isExceptionalZero
    {c : Real} (hc : 0 < c) {N : Nat} [NeZero N]
    (chi : _root_.DirichletCharacter Complex N) [NeZero chi.conductor]
    (hchi : Ne chi 1) {rho : Complex}
    (hExceptional : IsExceptionalZero c chi rho) :
    IsExceptionalZero c chi.primitiveCharacter rho := by
  have hdNat : 3 <= chi.conductor :=
    BombieriVinogradov.DirichletCharacter.three_le_conductor_of_ne_one chi hchi
  have hdReal : (3 : Real) <= (chi.conductor : Real) := Nat.cast_le.mpr hdNat
  have hdN : (chi.conductor : Real) <= (N : Real) :=
    Nat.cast_le.mpr (BombieriVinogradov.DirichletCharacter.conductor_le_level chi)
  have hThreshold : 1 - c / Real.log chi.conductor <= 1 - c / Real.log N :=
    BombieriVinogradov.RealAnalysis.logarithmicThreshold_mono
      hc.le (by linarith) hdN
  exact And.intro
    (primitive_LFunction_eq_zero_of_LFunction_eq_zero
      chi hchi hExceptional.2.2.1 hExceptional.1)
    (And.intro hExceptional.2.1
      (And.intro hExceptional.2.2.1
        (And.intro hExceptional.2.2.2.1
          (hThreshold.trans_lt hExceptional.2.2.2.2))))

end BombieriVinogradov.SiegelWalfisz

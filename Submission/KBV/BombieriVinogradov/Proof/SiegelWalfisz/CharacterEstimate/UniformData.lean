-- Vendored from kimihiro64/bombieri-vinogradov@7a174830 BombieriVinogradov/Proof/SiegelWalfisz/CharacterEstimate/UniformData.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.ZeroFreeData
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Uniform nonprincipal character estimate data

This named interface records the constants, their rate constraints,
the proved zero-free data and the complete character estimate separately.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

structure CharacterEstimateData (c a C : Real) : Prop where
  c_pos : 0 < c
  a_pos : 0 < a
  a_half : a <= (1 / 2 : Real)
  a_gap : 2 * a <= c / 4
  C_pos : 0 < C
  zeroFree : forall {N : Nat} [NeZero N] (chi : _root_.DirichletCharacter Complex N),
    Ne chi 1 -> ExplicitFormulaZeroFreeData c chi
  estimate : forall {N : Nat} [NeZero N] {chi : _root_.DirichletCharacter Complex N},
    Ne chi 1 -> forall {x : Nat}, 3 <= x ->
      (N : Real) <= Real.exp (Real.sqrt (Real.log x)) ->
        forall (e : Option Complex), IsExceptionalZeroChoice c chi e ->
          norm (characterChebyshevSum x chi + exceptionalZeroContribution x e) <=
            C * ((x : Real) * Real.exp (-(a * Real.sqrt (Real.log x))))

end BombieriVinogradov.SiegelWalfisz

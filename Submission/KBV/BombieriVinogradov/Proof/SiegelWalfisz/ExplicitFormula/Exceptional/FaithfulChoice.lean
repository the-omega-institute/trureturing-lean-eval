-- Vendored from kimihiro64/bombieri-vinogradov@7a174830 BombieriVinogradov/Proof/SiegelWalfisz/ExplicitFormula/Exceptional/FaithfulChoice.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Faithful exceptional choices at a fixed constant

Existence of the optional record needs no change to the chosen zero-free
constant. Analytical uniqueness and simplicity remain separate facts.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_faithfulExceptionalChoice (c : Real) {N : Nat} [NeZero N]
    (chi : _root_.DirichletCharacter Complex N) :
    exists e : Option Complex, IsExceptionalZeroChoice c chi e := by
  classical
  by_cases h : exists rho : Complex, IsExceptionalZero c chi rho
  case pos => exact Exists.intro (some h.choose) h.choose_spec
  case neg => exact Exists.intro none h

end BombieriVinogradov.SiegelWalfisz

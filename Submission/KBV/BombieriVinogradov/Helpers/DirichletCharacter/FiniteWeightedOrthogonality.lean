-- Vendored from kimihiro64/bombieri-vinogradov@7a174830 BombieriVinogradov/Helpers/DirichletCharacter/FiniteWeightedOrthogonality.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Tactic.Ring

/-!
# Finite weighted Dirichlet-character orthogonality

The exact Fourier expansion retains the totient coefficient and applies
to any finite natural index set, including non-coprime indices.
-/
set_option autoImplicit false

namespace BombieriVinogradov.DirichletCharacter

theorem sum_characters_weighted_eq_totient_mul_residue
    {N : Nat} [NeZero N] (a : Units (ZMod N))
    (s : Finset Nat) (f : Nat -> Complex) :
    Finset.sum Finset.univ (fun chi : _root_.DirichletCharacter Complex N =>
      chi (Inv.inv (a : ZMod N)) *
        Finset.sum s (fun n => f n * chi (n : ZMod N))) =
      (N.totient : Complex) *
        Finset.sum s (fun n => if (a : ZMod N) = (n : ZMod N) then f n else 0) := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _hn
  calc
    Finset.sum Finset.univ (fun chi : _root_.DirichletCharacter Complex N =>
        chi (Inv.inv (a : ZMod N)) * (f n * chi (n : ZMod N))) =
        f n * Finset.sum Finset.univ (fun chi : _root_.DirichletCharacter Complex N =>
          chi (Inv.inv (a : ZMod N)) * chi (n : ZMod N)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro chi _hchi
      ring
    _ = f n * (if (a : ZMod N) = (n : ZMod N) then (N.totient : Complex) else 0) := by
      rw [_root_.DirichletCharacter.sum_char_inv_mul_char_eq (R := Complex) a.isUnit]
    _ = (N.totient : Complex) *
        (if (a : ZMod N) = (n : ZMod N) then f n else 0) := by
      by_cases h : (a : ZMod N) = (n : ZMod N)
      case pos => rw [ite_eq_left h, ite_eq_left h]; ring
      case neg => rw [ite_eq_right h, ite_eq_right h]; ring

end BombieriVinogradov.DirichletCharacter

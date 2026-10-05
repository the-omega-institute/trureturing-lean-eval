-- Vendored from AxiomMath/PrimeGapsLib@1faa7b14 PrimeGapsTheory/ForMathlib/NumberTheory/ArithmeticFunction/Defs.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Defs

/-! # Arithmetic functions -/

public section

lemma ArithmeticFunction.natCoe_pow (n : ℕ) (f : ArithmeticFunction ℕ) (R : Type*) [CommRing R] :
    (f : ArithmeticFunction R) ^ n = ((f ^ n : ArithmeticFunction ℕ) : ArithmeticFunction R) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, ← natCoe_mul, ← pow_succ]

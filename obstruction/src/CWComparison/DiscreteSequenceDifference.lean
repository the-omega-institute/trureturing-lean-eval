/-
Copyright (c) 2026. Released under Apache 2.0.
The actual forward difference on the discrete reduced integral sequence is
not surjective. This is a source-level test of the localization obstruction
created by the EXACT protected CW scope; it is not a replacement comparison.
Uses Mathlib Finsupp linear combinations, Apache-2.0.
-/
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.Category.ModuleCat.Basic

noncomputable section

namespace CWComparison

/-- The discrete reduced sequence module and its genuine successor operator. -/
def discreteSequenceShift : (ℕ →₀ ℤ) →ₗ[ℤ] (ℕ →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ Nat.succ

/-- The total coefficient functional on the actual direct sum. -/
def discreteSequenceTotal : (ℕ →₀ ℤ) →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ (fun _ : ℕ => (1 : ℤ))

theorem discreteSequenceTotal_shift (x : ℕ →₀ ℤ) :
    discreteSequenceTotal (discreteSequenceShift x) = discreteSequenceTotal x := by
  exact LinearMap.congr_fun
    (Finsupp.linearCombination_comp_lmapDomain ℤ
      (v' := fun _ : ℕ => (1 : ℤ)) Nat.succ) x

/-- The canonical generator of total coefficient one cannot be a difference
of any FINITELY supported sequence. -/
theorem discreteSequenceDifference_not_surjective :
    ¬ Function.Surjective
      ((LinearMap.id : (ℕ →₀ ℤ) →ₗ[ℤ] (ℕ →₀ ℤ)) - discreteSequenceShift) := by
  intro h
  obtain ⟨x, hx⟩ := h (Finsupp.single 0 1)
  have he := congrArg discreteSequenceTotal hx
  simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub,
    discreteSequenceTotal_shift, sub_self] at he
  have hs : discreteSequenceTotal (Finsupp.single 0 1) = 1 := by
    simp [discreteSequenceTotal]
  rw [hs] at he
  exact zero_ne_one he

end CWComparison

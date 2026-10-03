import Submission.Transport

open UnitConjecture

set_option autoImplicit false

namespace Submission

/-- Gardam's Theorem A, with the exact official presentation and coefficients. -/
theorem theorem_A : (∀ g : P, ∀ n ≠ 0, g ^ n = 1 → g = 1) ∧ IsUnit u ∧ ¬ ∃ g : P, u = g := by
  exact ⟨Promislow.presented_torsion_free, Promislow.official_isUnit,
    Promislow.official_not_basis⟩

end Submission

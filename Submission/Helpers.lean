import ChallengeDeps
import Submission.DHJ.Solution

open Filter Finset
open LeanEval.Combinatorics
open scoped Classical

namespace Submission.Helpers

/-- Counting the elements of a set in the interval used by `upperDensity`. -/
lemma indicator_sum_eq_card (A : Set ℕ) (n : ℕ) :
    (∑ k ∈ range (n + 1), A.indicator (fun _ => (1 : ℝ)) k) =
      ((range (n + 1)).filter (· ∈ A)).card := by
  classical
  simp [Set.indicator]

/-- The initial-segment densities lie in the real unit interval. -/
lemma density_bounds (A : Set ℕ) (n : ℕ) :
    let u := (∑ k ∈ range (n + 1), A.indicator (fun _ => (1 : ℝ)) k) / (n + 1)
    0 ≤ u ∧ u ≤ 1 := by
  classical
  dsimp
  rw [indicator_sum_eq_card]
  constructor
  · positivity
  · apply (div_le_one (by positivity : (0 : ℝ) < n + 1)).2
    exact_mod_cast (card_filter_le (range (n + 1)) (· ∈ A)).trans_eq (card_range _)

/-- Positive upper density supplies dense initial segments beyond every threshold. -/
lemma exists_dense_initial_segment (A : Set ℕ) (h : 0 < upperDensity A) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ upperDensity A / 2 * (n + 1) ≤
      (((range (n + 1)).filter (· ∈ A)).card : ℝ) := by
  classical
  let u : ℕ → ℝ := fun n =>
    (∑ k ∈ range (n + 1), A.indicator (fun _ => (1 : ℝ)) k) / (n + 1)
  have hu : atTop.IsCoboundedUnder (· ≤ ·) u :=
    isCoboundedUnder_le_of_le atTop (fun n => (density_bounds A n).1)
  have hfreq : ∃ᶠ n in atTop, upperDensity A / 2 < u n :=
    frequently_lt_of_lt_limsup hu (by change upperDensity A / 2 < upperDensity A; linarith)
  obtain ⟨n, hn, hdense⟩ := frequently_atTop.mp hfreq N
  refine ⟨n, hn, ?_⟩
  have hnpos : (0 : ℝ) < n + 1 := by positivity
  dsimp [u] at hdense
  rw [indicator_sum_eq_card] at hdense
  exact le_of_lt ((lt_div_iff₀ hnpos).mp hdense)

end Submission.Helpers

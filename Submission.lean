import ChallengeDeps
import Submission.Helpers

open LeanEval.Combinatorics
open scoped BigOperators

namespace Submission

theorem szemeredi (A : Set ℕ) (h : 0 < upperDensity A) :
    ContainsArbitraryAPs A := by
  classical
  intro k
  let δ := upperDensity A / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (_root_.Combinatorics.ArithmeticProgression.exists_of_density_nat_atTop
      (max k 3) (Nat.le_max_right _ _) δ hδ)
  obtain ⟨n, hn, hdense⟩ := Helpers.exists_dense_initial_segment A h N
  let B := (Finset.range (n + 1)).filter (· ∈ A)
  obtain ⟨a, d, hd, hAP⟩ := hN (n + 1) (hn.trans (Nat.le_succ _)) B
    (Finset.filter_subset _ _)
    (by simpa only [δ, B, Nat.cast_add, Nat.cast_one] using hdense)
  refine ⟨a, d, Nat.one_le_iff_ne_zero.mpr hd, ?_⟩
  intro j hj
  have hj' : j < max k 3 := hj.trans_le (Nat.le_max_left _ _)
  have hmem := hAP ⟨j, hj'⟩
  exact (Finset.mem_filter.mp (by simpa only [Nat.mul_comm] using hmem)).2

end Submission

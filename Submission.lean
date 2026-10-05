import Mathlib
import Lake.Toml
import Lake.Util.Message
import Lean
import Submission.Helpers
import Submission.PGL.PrimeGaps.Bounded246
import Submission.KBV.Solution

open Filter Finset MeasureTheory
open scoped BigOperators Topology

namespace Submission

theorem zhang_bounded_prime_gaps :
    ∀ n : ℕ, ∃ p q : ℕ, n ≤ p ∧ p.Prime ∧ q.Prime ∧ p < q ∧ q - p ≤ 246 := by
  intro n
  have hBV : _root_.BombieriVinogradov :=
    BombieriVinogradov.bombieriVinogradov
  obtain ⟨p, q, hnp, hpq, hp, hq, hgap⟩ :=
    bombieriVinogradov_implies_prime_gap_le_246 hBV n
  exact ⟨p, q, hnp, hp, hq, hpq, by omega⟩

end Submission

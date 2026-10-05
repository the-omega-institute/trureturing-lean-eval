import Mathlib
import Lake.Toml
import Lake.Util.Message
import Lean
import Submission.Helpers
import Submission.L10.FinalTheorem

namespace Submission

theorem klartag_packing : ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
    let V := EuclideanSpace ℝ (Fin (n + 1))
    ∃ φ : V →ₗ[ℝ] V, let E := φ '' Metric.ball (0 : V) 1
      (MeasureTheory.volume E : EReal) = c * n ^ 2 ∧
      {v ∈ E | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} := by
  exact Submission.L10.FinalTheorem.klartag_packing_final

end Submission

import Mathlib
import Lake.Toml
import Lake.Util.Message
import Lean
import Submission.Helpers
import Submission.DifferentialGeometry.Topology.HighDimensional.PoincareHighDim

open Metric (sphere)
open ContinuousMap

namespace Submission

theorem poincare_high_dim_topological {n : ℕ} (_h5 : 5 ≤ n)
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (_h : M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    Nonempty (M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  exact DifferentialGeometry.Topology.poincare_high_dim_topological _h5 _h

end Submission

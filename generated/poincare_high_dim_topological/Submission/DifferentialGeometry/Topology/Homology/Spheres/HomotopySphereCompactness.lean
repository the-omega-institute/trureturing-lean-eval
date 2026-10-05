/- Relocated from qinz1yang/differential-geometry at 788efe97894474c032de6dfb1289d515f613d15a.
   Modified only by prefixing local module imports with Submission.;
   namespaces, declarations, proof bodies and import flags are preserved.
   Apache-2.0; see LICENSE and NOTICE in this workspace. -/
import Submission.DifferentialGeometry.Topology.Homology.Local.Noncompact
import Submission.DifferentialGeometry.Topology.Homology.Spheres.CompactZero

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff ContinuousMap
open Metric

theorem compactSpace_of_homotopyEquiv_sphere {n : ℕ} {M : Type*} [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (e : M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) : CompactSpace M := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact SingularPair.compactSpace_of_homotopyEquiv_sphere_zero e
  · exact SingularPair.compactSpace_of_homotopyEquiv_sphere_of_one_le hn e

end DifferentialGeometry.Topology

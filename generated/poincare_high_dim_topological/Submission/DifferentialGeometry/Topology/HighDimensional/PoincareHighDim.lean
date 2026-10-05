/- Relocated from qinz1yang/differential-geometry at 788efe97894474c032de6dfb1289d515f613d15a.
   Modified only by prefixing local module imports with Submission.;
   namespaces, declarations, proof bodies and import flags are preserved.
   Apache-2.0; see LICENSE and NOTICE in this workspace. -/
import Submission.DifferentialGeometry.Topology.Homology.Spheres.HomotopySphereCompactness
import Submission.DifferentialGeometry.Topology.Engulfing.NewmanTheorem
import Submission.DifferentialGeometry.Topology.HighDimensional.RelativeEngulfing

open Metric (sphere)
open ContinuousMap

namespace DifferentialGeometry.Topology

theorem poincare_high_dim_topological {n : ℕ} (h5 : 5 ≤ n)
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (h : M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    Nonempty (M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  let : CompactSpace M := compactSpace_of_homotopyEquiv_sphere h
  exact nonempty_homeomorph_sphere_of_uniform_relativeNewman h5 h
    (fun N _ q => Engulfing.relative_newman_at N n (n - 3) q)

end DifferentialGeometry.Topology

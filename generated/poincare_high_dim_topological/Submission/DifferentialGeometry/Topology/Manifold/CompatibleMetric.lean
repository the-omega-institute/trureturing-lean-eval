/- Relocated from qinz1yang/differential-geometry at 788efe97894474c032de6dfb1289d515f613d15a.
   Modified only by prefixing local module imports with Submission.;
   namespaces, declarations, proof bodies and import flags are preserved.
   Apache-2.0; see LICENSE and NOTICE in this workspace. -/
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.Metrizable.Uniformity

namespace DifferentialGeometry.Topology

open TopologicalSpace

theorem metrizableSpace_of_compact_charted {n : ℕ} {M : Type*}
    [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] : MetrizableSpace M := by
  let : SecondCountableTopology M :=
    ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin n)) M
  infer_instance

end DifferentialGeometry.Topology

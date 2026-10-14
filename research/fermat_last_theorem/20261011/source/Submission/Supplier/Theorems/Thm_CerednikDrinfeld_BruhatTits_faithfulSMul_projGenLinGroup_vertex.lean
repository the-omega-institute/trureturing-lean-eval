import Submission.Supplier.Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Algebra.Group.Action.Faithful
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_CerednikDrinfeld_BruhatTits_faithfulSMul_projGenLinGroup_vertex

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open CerednikDrinfeld.BruhatTits LT.LatticeTree

theorem CerednikDrinfeld.BruhatTits.faithfulSMul_projGenLinGroup_vertex
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] :
    FaithfulSMul (Matrix.ProjGenLinGroup (Fin 2) K) (Vertex R K) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_BruhatTits_faithfulSMul_projGenLinGroup_vertex.solution

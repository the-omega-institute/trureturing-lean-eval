import Submission.Supplier.Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Mathlib.Combinatorics.SimpleGraph.Metric
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_CerednikDrinfeld_Mumford_GraphAction_dist_smul_smul

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

theorem CerednikDrinfeld.Mumford.GraphAction.dist_smul_smul
    {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W)
    [CerednikDrinfeld.Mumford.GraphAction G 𝒯] (g : G) (x y : W) :
    𝒯.dist (g • x) (g • y) = 𝒯.dist x y := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Mumford_GraphAction_dist_smul_smul.solution

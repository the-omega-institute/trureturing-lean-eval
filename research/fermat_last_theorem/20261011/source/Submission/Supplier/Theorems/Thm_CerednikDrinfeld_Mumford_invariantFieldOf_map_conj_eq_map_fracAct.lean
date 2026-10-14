import Submission.Supplier.Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_CerednikDrinfeld_Mumford_invariantFieldOf_map_conj_eq_map_fracAct

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Mumford.invariantFieldOf_map_conj_eq_map_fracAct
    (K : Type) [Field K] (G : Type) [Group G] (M : Type) [CommRing M] [Algebra K M]
    [MulSemiringAction G M] [SMulCommClass G K M] [IsDomain M] (g : G) (Γ : Subgroup G) :
    invariantFieldOf K G M (Γ.map (MulAut.conj g).toMonoidHom) =
      (invariantFieldOf K G M Γ).map (fracAct G M g).toRingHom := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Mumford_invariantFieldOf_map_conj_eq_map_fracAct.solution

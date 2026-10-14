import Submission.Supplier.Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_CerednikDrinfeld_Omega_apply_mem_map_of_forall_exists_pmoebius_eq_pmoebius

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.apply_mem_map_of_forall_exists_pmoebius_eq_pmoebius
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    (hunc : ¬ (Omega.upperHalfPlane K₀ K).Countable)
    (G : Type) [Group G] (ρ : G →* PGL(2, K₀))
    (Δ : Subgroup G) (hcount : Countable ↥(Δ.map ρ))
    (g : G)
    (hg : ∀ z ∈ Omega.upperHalfPlane K₀ K, ∃ δ ∈ Δ, Omega.pmoebius K₀ (ρ g) z = Omega.pmoebius K₀ (ρ δ) z) :
    ρ g ∈ Δ.map ρ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_apply_mem_map_of_forall_exists_pmoebius_eq_pmoebius.solution

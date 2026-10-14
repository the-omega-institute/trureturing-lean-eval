import Mathlib
import Submission.Supplier.Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_CerednikDrinfeld_Omega_crossRatio_pmoebius

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.crossRatio_pmoebius
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K]
    (g : PGL(2, K₀)) {z z₀ x y : K}
    (hz : z ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)
    (hx : x ∈ upperHalfPlane K₀ K) (hy : y ∈ upperHalfPlane K₀ K) :
    crossRatio (pmoebius K₀ g z) (pmoebius K₀ g z₀) (pmoebius K₀ g x) (pmoebius K₀ g y) = crossRatio z z₀ x y := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Omega_crossRatio_pmoebius.solution

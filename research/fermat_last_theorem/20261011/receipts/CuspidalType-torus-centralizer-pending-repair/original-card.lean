import Mathlib
import Submission.Supplier.Definitions.Def_CuspidalType_IsCuspidalOfType
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_CuspidalType_mul_torus_eq_torus_mul_iff

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open Polynomial CuspidalType

theorem CuspidalType.mul_torus_eq_torus_mul_iff (q : ℕ) [Fact q.Prime] {α : (GaloisField q 2)ˣ}
    (hα : (α : GaloisField q 2) ∉ Set.range (algebraMap (ZMod q) (GaloisField q 2))) (h : GL2 q) :
    h * torus q α = torus q α * h ↔ h ∈ (torus q).range := by p2m_exact_reverting @_root_.P2MW.S_CuspidalType_mul_torus_eq_torus_mul_iff.solution

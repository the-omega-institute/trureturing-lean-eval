import Mathlib
import Submission.Supplier.Definitions.Def_CuspidalType_IsCuspidalOfType
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_CuspidalType_charpoly_ind_torus_eq_X_pow_orderOf_sub_one_pow

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open Polynomial CuspidalType

theorem CuspidalType.charpoly_ind_torus_eq_X_pow_orderOf_sub_one_pow
    (q : ℕ) [Fact q.Prime] (K : Type*) [Field K] (α : (GaloisField q 2)ˣ) :
    LinearMap.charpoly (ind q K (torus q α)) =
      (X ^ orderOf (MulAction.toPermHom (GL2 q) (ProjLine q) (torus q α)) - 1) ^
        ((q + 1) / orderOf (MulAction.toPermHom (GL2 q) (ProjLine q) (torus q α))) := by p2m_exact_reverting @_root_.P2MW.S_CuspidalType_charpoly_ind_torus_eq_X_pow_orderOf_sub_one_pow.solution

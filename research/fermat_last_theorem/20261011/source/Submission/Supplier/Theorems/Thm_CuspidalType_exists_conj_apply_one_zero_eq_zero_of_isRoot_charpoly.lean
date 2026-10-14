import Mathlib
import Submission.Supplier.Definitions.Def_CuspidalType_IsCuspidalOfType
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_CuspidalType_exists_conj_apply_one_zero_eq_zero_of_isRoot_charpoly

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open Polynomial CuspidalType

theorem CuspidalType.exists_conj_apply_one_zero_eq_zero_of_isRoot_charpoly
    (q : ℕ) [Fact q.Prime]
    (g : GL2 q) (x : ZMod q)
    (hx : (g : Matrix (Fin 2) (Fin 2) (ZMod q)).charpoly.IsRoot x) :
    ∃ h : GL2 q, ((h * g * h⁻¹ : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 = 0 := by p2m_exact_reverting @_root_.P2MW.S_CuspidalType_exists_conj_apply_one_zero_eq_zero_of_isRoot_charpoly.solution

#print axioms CuspidalType.exists_conj_apply_one_zero_eq_zero_of_isRoot_charpoly

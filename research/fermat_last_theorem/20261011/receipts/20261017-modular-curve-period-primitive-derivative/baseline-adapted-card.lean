import Mathlib
import Submission.Supplier.Definitions.Def_ModularCurve_PeriodOf
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_ModularCurve_periodOf_apply_eq_sub_of_hasEquivariantPrimitiveOf

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.periodOf_apply_eq_sub_of_hasEquivariantPrimitiveOf (Γ : Subgroup SL(2, ℤ))
    (f : CuspForm Γ 2) {F : UpperHalfPlane → ℂ}
    (hF : ModularCurve.HasEquivariantPrimitiveOf Γ f F) (γ : Γ) :
    ModularCurve.periodOf Γ γ f =
      F ((γ : SL(2, ℤ)) • UpperHalfPlane.I) - F UpperHalfPlane.I := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_periodOf_apply_eq_sub_of_hasEquivariantPrimitiveOf.solution

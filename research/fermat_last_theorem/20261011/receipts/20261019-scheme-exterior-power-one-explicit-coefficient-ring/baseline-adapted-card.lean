import Mathlib
import Submission.Supplier.Definitions.Def_AlgebraicGeometry_ModulesDet
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_nonempty_exteriorPower_one_iso_id

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.nonempty_exteriorPower_one_iso_id (X : Scheme.{u}) :
    Nonempty (Scheme.Modules.exteriorPower X 1 ≅ 𝟭 X.Modules) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_exteriorPower_one_iso_id.solution

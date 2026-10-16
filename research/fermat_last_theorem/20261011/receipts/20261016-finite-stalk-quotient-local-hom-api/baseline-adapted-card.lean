import Mathlib
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_AlgebraicGeometry_IsFinite_ringKrullDim_stalk_quotient_eq_zero

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

theorem AlgebraicGeometry.IsFinite.ringKrullDim_stalk_quotient_eq_zero
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsFinite g] [IsLocallyNoetherian Y] (x : X) :
    ringKrullDim ((X.presheaf.stalk x) ⧸
      (maximalIdeal (Y.presheaf.stalk (g.base x))).map (g.stalkMap x).hom) = 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_IsFinite_ringKrullDim_stalk_quotient_eq_zero.solution

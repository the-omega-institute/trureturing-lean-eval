import Mathlib
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_AlgebraicGeometry_Smooth_exists_smoothOfRelativeDimension_of_preconnectedSpace

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

open AlgebraicGeometry CategoryTheory

universe u

theorem AlgebraicGeometry.Smooth.exists_smoothOfRelativeDimension_of_preconnectedSpace
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] [PreconnectedSpace X] :
    ∃ n : ℕ, SmoothOfRelativeDimension n f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Smooth_exists_smoothOfRelativeDimension_of_preconnectedSpace.solution

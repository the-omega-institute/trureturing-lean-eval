import Mathlib
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_AlgebraicGeometry_GeometricallyConnected_descendsAlong_surjective

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

universe u

open CategoryTheory MorphismProperty AlgebraicGeometry

theorem AlgebraicGeometry.GeometricallyConnected.descendsAlong_surjective :
    DescendsAlong (@GeometricallyConnected : MorphismProperty Scheme.{u}) @Surjective := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_GeometricallyConnected_descendsAlong_surjective.solution

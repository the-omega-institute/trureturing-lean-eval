import Mathlib
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_AlgebraicGeometry_Scheme_finite_of_isClosed_of_genericPoint_notMem

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

theorem AlgebraicGeometry.Scheme.finite_of_isClosed_of_genericPoint_notMem {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [CompactSpace X]
    (hdim : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 1)
    {Z : Set X} (hZ : IsClosed Z) (hη : genericPoint X ∉ Z) : Z.Finite := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_finite_of_isClosed_of_genericPoint_notMem.solution

import Mathlib
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_AlgebraicGeometry_isOpen_irreducibleComponent_of_isDomain_stalk

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

theorem AlgebraicGeometry.isOpen_irreducibleComponent_of_isDomain_stalk
    {X : Scheme.{u}} [IsLocallyNoetherian X] (hX : ∀ x : X, IsDomain (X.presheaf.stalk x)) (x : X) :
    IsOpen (irreducibleComponent x) ∧ ∀ Z ∈ irreducibleComponents X, x ∈ Z → Z = irreducibleComponent x := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isOpen_irreducibleComponent_of_isDomain_stalk.solution

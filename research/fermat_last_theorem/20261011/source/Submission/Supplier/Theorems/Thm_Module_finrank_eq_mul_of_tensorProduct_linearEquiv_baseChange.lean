import Mathlib
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_Module_finrank_eq_mul_of_tensorProduct_linearEquiv_baseChange

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open TensorProduct

universe u

theorem Module.finrank_eq_mul_of_tensorProduct_linearEquiv_baseChange
    {κ : Type u} [Field κ] {B C D : Type u} [CommRing B] [CommRing C] [Algebra κ B] [Algebra κ C]
    [Algebra B C] [IsScalarTower κ B C] [AddCommGroup D] [Module κ D]
    [Module.Finite κ B] [Module.Finite κ C] [Module.Finite κ D] [Module.FaithfullyFlat B C]
    (e : C ⊗[B] C ≃ₗ[C] C ⊗[κ] D) :
    Module.finrank κ C = Module.finrank κ D * Module.finrank κ B := by p2m_exact_reverting @_root_.P2MW.S_Module_finrank_eq_mul_of_tensorProduct_linearEquiv_baseChange.solution

import Mathlib
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_Algebra_norm_one_add_eps_tmul

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

universe u

open scoped TensorProduct

theorem Algebra.norm_one_add_eps_tmul
    (A' B : Type u) [CommRing A'] [CommRing B] [Algebra A' B] [Module.Free A' B] [Module.Finite A' B] (f : B) :
    Algebra.norm (DualNumber A') ((1 : DualNumber A' ⊗[A'] B) + (DualNumber.eps : DualNumber A') ⊗ₜ[A'] f) =
      1 + TrivSqZeroExt.inr (Algebra.trace A' B f) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_norm_one_add_eps_tmul.solution

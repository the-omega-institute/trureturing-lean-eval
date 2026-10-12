import Mathlib
import Submission.Supplier.Definitions.Def_ModularCurve_JqCoeff
import Submission.Supplier.Definitions.Def_ModularCurve_LaurentCoeff
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_ModularCurve_exists_algHom_tensorProduct_modularFunctionFieldC_injective

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open scoped TensorProduct

theorem ModularCurve.exists_algHom_tensorProduct_modularFunctionFieldC_injective
    (κ₀ κ : Type*) [Field κ₀] [Field κ] [Algebra κ₀ κ] (N : ℕ) [NeZero N] :
    ∃ f : κ ⊗[κ₀] ↥(modularFunctionFieldC κ₀ N) →ₐ[κ] LaurentSeries κ,
      (∀ (x : κ) (g : ↥(modularFunctionFieldC κ₀ N)),
          f (x ⊗ₜ[κ₀] g) = x • ModularCurve.coeffMap (algebraMap κ₀ κ) (g : LaurentSeries κ₀)) ∧
      Function.Injective f ∧
      (∀ z, f z ∈ modularFunctionFieldC κ N) ∧
      (∀ y ∈ modularFunctionFieldC κ N, ∃ a b, f b ≠ 0 ∧ y * f b = f a) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_algHom_tensorProduct_modularFunctionFieldC_injective.solution

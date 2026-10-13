import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_Module_End_maxGenEigenspace_baseChange_le_eigenspace_of_isAlgClosed

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

theorem Module.End.maxGenEigenspace_baseChange_le_eigenspace_of_isAlgClosed
    {K : Type} [Field K] [CharZero K] {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (T : Module.End K W)
    (Ω₁ : Type) [Field Ω₁] [Algebra K Ω₁] [IsAlgClosed Ω₁]
    (h₁ : ∀ μ : Ω₁, Module.End.maxGenEigenspace (T.baseChange Ω₁) μ ≤
      Module.End.eigenspace (T.baseChange Ω₁) μ)
    (Ω₂ : Type) [Field Ω₂] [Algebra K Ω₂] (μ : Ω₂) :
    Module.End.maxGenEigenspace (T.baseChange Ω₂) μ ≤ Module.End.eigenspace (T.baseChange Ω₂) μ := by p2m_exact_reverting @_root_.P2MW.S_Module_End_maxGenEigenspace_baseChange_le_eigenspace_of_isAlgClosed.solution

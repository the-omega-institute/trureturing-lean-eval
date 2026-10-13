import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Polynomial.Roots
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_Module_End_finrank_iInf_maxGenEigenspace_baseChange_eq_mul_prod_rootMultiplicity_of_isAlgClosed

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open Polynomial

theorem Module.End.finrank_iInf_maxGenEigenspace_baseChange_eq_mul_prod_rootMultiplicity_of_isAlgClosed
    {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {Q : Type} [Fintype Q] (U : Q → Module.End K W) (P : Q → Polynomial K) (c : ℕ)
    (Ω₁ : Type) [Field Ω₁] [Algebra K Ω₁] [IsAlgClosed Ω₁]
    (h₁ : ∀ μ : Q → Ω₁, Module.finrank Ω₁
        ↥(⨅ q, Module.End.maxGenEigenspace ((U q).baseChange Ω₁) (μ q)) =
      c * ∏ q, Polynomial.rootMultiplicity (μ q) ((P q).map (algebraMap K Ω₁)))
    (Ω₂ : Type) [Field Ω₂] [Algebra K Ω₂] (lam : Q → Ω₂) :
    Module.finrank Ω₂ ↥(⨅ q, Module.End.maxGenEigenspace ((U q).baseChange Ω₂) (lam q)) =
      c * ∏ q, Polynomial.rootMultiplicity (lam q) ((P q).map (algebraMap K Ω₂)) := by p2m_exact_reverting @_root_.P2MW.S_Module_End_finrank_iInf_maxGenEigenspace_baseChange_eq_mul_prod_rootMultiplicity_of_isAlgClosed.solution

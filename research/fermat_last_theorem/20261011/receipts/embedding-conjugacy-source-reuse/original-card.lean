import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Pi
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_AlgHom_exists_algEquiv_comp_eq_of_isAlgClosed

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

theorem AlgHom.exists_algEquiv_comp_eq_of_isAlgClosed
    {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω]
    [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    {M : Type*} [Field M] [Algebra K M] (σ τ : M →ₐ[K] Ω) :
    ∃ γ : Ω ≃ₐ[K] Ω, γ.toAlgHom.comp σ = τ := by p2m_exact_reverting @_root_.P2MW.S_AlgHom_exists_algEquiv_comp_eq_of_isAlgClosed.solution

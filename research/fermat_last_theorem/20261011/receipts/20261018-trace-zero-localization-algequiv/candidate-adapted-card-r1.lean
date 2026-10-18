import Mathlib
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_AlgebraicGeometry_trace_eq_zero_of_finrank_eq_char_of_forall_isClosed_eq

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.trace_eq_zero_of_finrank_eq_char_of_forall_isClosed_eq
    {κ : Type u} [Field κ] [IsAlgClosed κ] {p : ℕ} [Fact p.Prime] [CharP κ p]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (fY : Y ⟶ Spec (CommRingCat.of κ)) [LocallyOfFiniteType fY]
    (f : X ⟶ Y) [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] (hrk : ∀ y, f.finrank y = p)
    (hinj : ∀ x₁ x₂ : X, IsClosed ({x₁} : Set X) → IsClosed ({x₂} : Set X) → f.base x₁ = f.base x₂ → x₁ = x₂)
    (U : Y.Opens) (hU : IsAffineOpen U) :
    letI := (f.app U).hom.toAlgebra
    ∀ [Module.Free Γ(Y, U) Γ(X, f ⁻¹ᵁ U)] [Module.Finite Γ(Y, U) Γ(X, f ⁻¹ᵁ U)],
      Algebra.trace Γ(Y, U) Γ(X, f ⁻¹ᵁ U) = 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_trace_eq_zero_of_finrank_eq_char_of_forall_isClosed_eq.solution

#print axioms AlgebraicGeometry.trace_eq_zero_of_finrank_eq_char_of_forall_isClosed_eq

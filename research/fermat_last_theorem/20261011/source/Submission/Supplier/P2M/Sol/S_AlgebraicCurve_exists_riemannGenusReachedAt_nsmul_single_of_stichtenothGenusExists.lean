import Mathlib
import Submission.Supplier.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Submission.Supplier.Definitions.Def_AlgebraicCurve_IsCurveOver
import Submission.Supplier.Definitions.Def_AlgebraicCurve_Repartitions
import Submission.Supplier.Definitions.Def_AlgebraicCurve_AdelicIndex
import Submission.Supplier.Theorems.Thm_AlgebraicCurve_exists_indexOfSpecialty_nsmul_single_eq_zero_of_genusReached
import Submission.Supplier.Theorems.Thm_AlgebraicCurve_indexOfSpecialty_eq_of_genusReached
import Submission.Supplier.Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace
import Submission.Supplier.P2M.Util

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
namespace P2MW.S_AlgebraicCurve_exists_riemannGenusReachedAt_nsmul_single_of_stichtenothGenusExists

set_option autoImplicit false
set_option maxHeartbeats 4000000

open AlgebraicCurve

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    [Nonempty (Place K F)] [FiniteDimensional K ↥(LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) (Q : Place K F) :
    ∃ n : ℕ, RiemannGenusReachedAt γ ((n : ℤ) • Finsupp.single Q 1) := by
  classical
  obtain ⟨n, hn⟩ :=
    exists_indexOfSpecialty_nsmul_single_eq_zero_of_genusReached h Q
  refine ⟨n, ?_⟩
  have hidx := (indexOfSpecialty_eq_of_genusReached h
    ((n : ℤ) • Finsupp.single Q (1 : ℤ))).2
  rw [hn] at hidx
  have heq : Divisor.degree ((n : ℤ) • Finsupp.single Q (1 : ℤ)) -
      (ell ((n : ℤ) • Finsupp.single Q (1 : ℤ)) : ℤ) = γ - 1 := by
    push_cast at hidx ⊢
    linarith
  exact ⟨finiteDimensional_lSpace _, heq, h.isMax⟩

#print axioms P2MW.S_AlgebraicCurve_exists_riemannGenusReachedAt_nsmul_single_of_stichtenothGenusExists.solution

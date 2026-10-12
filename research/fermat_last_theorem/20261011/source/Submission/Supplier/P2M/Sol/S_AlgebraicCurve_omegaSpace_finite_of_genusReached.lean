import Submission.Supplier.P2M.Sol.S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

-- Reuse the checked supplier theorem with the complete original solution declaration.
namespace P2MW.S_AlgebraicCurve_omegaSpace_finite_of_genusReached

set_option autoImplicit false

open _root_.P2MW.S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.AlgebraicCurve

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F] [Nonempty (Place K F)] [FiniteDimensional K ↥(LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) (D : Divisor K F) :
    Module.Finite K ↥(omegaSpace (K := K) (F := F) D) :=
  _root_.P2MW.S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.AlgebraicCurve.omegaSpace_finite_of_genusReached (K := K) (F := F) h D

end P2MW.S_AlgebraicCurve_omegaSpace_finite_of_genusReached

#print axioms P2MW.S_AlgebraicCurve_omegaSpace_finite_of_genusReached.solution

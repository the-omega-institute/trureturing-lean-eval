import P2M.Sol.S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists

-- Reuse the checked supplier theorem with the complete original solution declaration.
namespace P2MW.S_AlgebraicCurve_omegaSpace_finite_of_genusReached

set_option autoImplicit false

open _root_.P2MW.S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.AlgebraicCurve

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F] [Nonempty (Place K F)] [FiniteDimensional K ↥(LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) (D : Divisor K F) :
    Module.Finite K ↥(omegaSpace (K :=
  _root_.P2MW.S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.AlgebraicCurve.omegaSpace_finite_of_genusReached (K := K) (F := F) h D

end P2MW.S_AlgebraicCurve_omegaSpace_finite_of_genusReached

import P2M.Sol.S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists

-- Reuse the checked supplier theorem with the complete original solution declaration.
namespace P2MW.S_AlgebraicCurve_linearIndependent_pow_mul

set_option autoImplicit false

open _root_.P2MW.S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.AlgebraicCurve

theorem solution {K : Type*} {E : Type*} {F : Type*} [Field K] [Field E] [Field F] [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F] {x : E} {n : ℕ} {u : Fin n → F}
    (hx : LinearIndependent K (fun j : ℕ => x ^ j)) (hu : LinearIndependent E u) :
    LinearIndependent K (fun p : ℕ × Fin n => (algebraMap E F x) ^ p.1 * u p.2) :=
  _root_.P2MW.S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.AlgebraicCurve.linearIndependent_pow_mul (K := K) (E := E) (F := F) hx hu

end P2MW.S_AlgebraicCurve_linearIndependent_pow_mul

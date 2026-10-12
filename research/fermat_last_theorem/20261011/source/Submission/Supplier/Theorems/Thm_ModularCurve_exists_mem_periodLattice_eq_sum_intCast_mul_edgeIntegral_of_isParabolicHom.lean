import Mathlib
import Submission.Supplier.Definitions.Def_ModularCurve_PeriodLattice
import Submission.Supplier.Definitions.Def_ModularCurve_PeriodMap
import Submission.Supplier.Definitions.Def_AutomorphicForm_Gamma0FundamentalSet
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_ModularCurve_exists_mem_periodLattice_eq_sum_intCast_mul_edgeIntegral_of_isParabolicHom

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups

theorem ModularCurve.exists_mem_periodLattice_eq_sum_intCast_mul_edgeIntegral_of_isParabolicHom
    {N : ℕ} [NeZero N] [Fintype (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)]
    (γT γS : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → CongruenceSubgroup.Gamma0 N)
    (hT : ∀ q, ((γT q : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) =
      (Quotient.out (ModularGroup.T • q))⁻¹ * ModularGroup.T * Quotient.out q)
    (hS : ∀ q, ((γS q : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) =
      (Quotient.out (ModularGroup.S • q))⁻¹ * ModularGroup.S * Quotient.out q)
    (φ : Additive (CongruenceSubgroup.Gamma0 N) →+ ℤ)
    (hφ : ModularCurve.Period.IsParabolicHom (CongruenceSubgroup.Gamma0 N) φ) :
    ∃ Λ ∈ ModularCurve.periodLattice N,
      ∀ (g : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
        (G : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → ℂ → ℂ),
        (∀ q z, G q z = g ((Quotient.out q)⁻¹ • ofComplex z) /
          denom (((Quotient.out q)⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) (ofComplex z) ^ 2) →
        Complex.I * ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
              ((φ (Additive.ofMul (γT q)) : ℤ) : ℂ) *
                (∫ y in Set.Ioi (Real.sqrt 3 / 2), G q (-(1 / 2) + y * Complex.I)) +
            1 / 2 * ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
              ((φ (Additive.ofMul (γS q)) : ℤ) : ℂ) *
                (∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
                  G q (Complex.exp (θ * Complex.I)) * (Complex.I * Complex.exp (θ * Complex.I))) =
          Λ g := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_mem_periodLattice_eq_sum_intCast_mul_edgeIntegral_of_isParabolicHom.solution

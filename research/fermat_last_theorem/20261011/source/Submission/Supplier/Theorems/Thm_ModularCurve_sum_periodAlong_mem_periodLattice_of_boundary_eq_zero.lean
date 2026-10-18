import Mathlib
import Submission.Supplier.Definitions.Def_ModularCurve_PeriodLattice
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_ModularCurve_sum_periodAlong_mem_periodLattice_of_boundary_eq_zero

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
attribute [-simp] ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one

open UpperHalfPlane
open scoped MatrixGroups

open Classical in

theorem ModularCurve.sum_periodAlong_mem_periodLattice_of_boundary_eq_zero
    {N : ℕ} [NeZero N] (Z : (ℍ × ℍ) →₀ ℤ)
    (hZ : ∀ τ : ℍ,
      Z.sum (fun e m =>
        (if ∃ γ : CongruenceSubgroup.Gamma0 N, (γ : SL(2, ℤ)) • e.2 = τ then m else 0) -
        (if ∃ γ : CongruenceSubgroup.Gamma0 N, (γ : SL(2, ℤ)) • e.1 = τ then m else 0)) = 0) :
    (Z.sum fun e m => m • ModularCurve.periodAlong N e.1 e.2) ∈
      ModularCurve.periodLattice N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_sum_periodAlong_mem_periodLattice_of_boundary_eq_zero.solution

#print axioms ModularCurve.sum_periodAlong_mem_periodLattice_of_boundary_eq_zero

import Submission.Supplier.Definitions.Def_ModularCurve_PeriodMapBundled
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_ModularCurve_Period_CuspForm_exists_equivariantPrimitive_gamma0

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

open scoped MatrixGroups
theorem ModularCurve.Period.CuspForm.exists_equivariantPrimitive_gamma0 {N : ℕ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    ∃ Fprim : UpperHalfPlane → ℂ,
      (∀ τ : UpperHalfPlane, HasDerivAt (Fprim ∘ UpperHalfPlane.ofComplex) (f τ) ↑τ) ∧
      Filter.Tendsto Fprim UpperHalfPlane.atImInfty (nhds 0) ∧
      ModularCurve.Period.IsEquivariantPrimitive (CongruenceSubgroup.Gamma0 N) Fprim ∧
      ∀ δ : SL(2, ℤ), ∃ L : ℂ,
        Filter.Tendsto (fun w : UpperHalfPlane => Fprim (δ • w)) UpperHalfPlane.atImInfty (nhds L) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_Period_CuspForm_exists_equivariantPrimitive_gamma0.solution

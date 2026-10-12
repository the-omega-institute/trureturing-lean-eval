import Mathlib
import Submission.Supplier.Definitions.Def_AutomorphicForm_Gamma0FundamentalSet
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_ModularCurve_exists_cuspForm_petersson_eq

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups

theorem ModularCurve.exists_cuspForm_petersson_eq {N : ℕ} [NeZero N]
    (ℓ : Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) :
    ∃ f : CuspForm (CongruenceSubgroup.Gamma0 N) 2,
      ∀ g : CuspForm (CongruenceSubgroup.Gamma0 N) 2,
        Complex.I * (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet
          (CongruenceSubgroup.Gamma0 N), UpperHalfPlane.petersson 2 f g τ) = ℓ g := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_cuspForm_petersson_eq.solution

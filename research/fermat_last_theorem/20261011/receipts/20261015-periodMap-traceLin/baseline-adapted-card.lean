import Submission.Supplier.Definitions.Def_ModularCurve_PeriodMapBundled
import Submission.Supplier.Definitions.Def_CuspForm_LevelLoweringTrace
import Submission.Supplier.Definitions.Def_Gamma0HeckeOperatorHom
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_ModularCurve_periodMap_traceLin

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false
open CongruenceSubgroup

theorem ModularCurve.periodMap_traceLin {M q : ℕ} [NeZero M] (W : ModularForm.AtkinLehnerDatum M q)
    (hq : q.Prime) (f : CuspForm (Gamma0 M) 2) :
    ModularCurve.periodMap W.R (CuspForm.traceLin W hq f) =
      HeckeEis.coresHom ((Gamma0 M).subgroupOf (Gamma0 W.R))
        (HeckeEis.pullbackHom ((Gamma0 W.R).subtype.subgroupComap (Gamma0 M))
          (ModularCurve.periodMap M f)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_periodMap_traceLin.solution

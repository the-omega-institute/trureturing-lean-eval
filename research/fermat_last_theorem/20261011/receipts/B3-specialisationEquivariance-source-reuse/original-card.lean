import Submission.Supplier.Definitions.Def_ModularCurve_SpecialisationBridge
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_ModularCurve_B3_b3_specialisationEquivariance

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

open ModularCurve ModularCurve.TatePoint ModularCurve.B3
theorem ModularCurve.B3.b3_specialisationEquivariance (p : ℕ) [Fact p.Prime] [NeZero p] (j₀ : Qbar) :
    ∃ β : CycSubH (nearCurve j₀) p ≃ CycSub (WeierstrassCurve.ofJ j₀) p,
      ∀ G G' : CycSubH (nearCurve j₀) p,
        (∃ m : HahnSeries.monodromy Qbar, b3Act j₀ m G.1 = G'.1) ↔
          SameOrbit (WeierstrassCurve.ofJ j₀) (β G).1 (β G').1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_B3_b3_specialisationEquivariance.solution

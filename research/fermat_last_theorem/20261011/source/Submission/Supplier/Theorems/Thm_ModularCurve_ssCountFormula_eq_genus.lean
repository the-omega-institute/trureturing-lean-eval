import Mathlib
import Submission.Supplier.Definitions.Def_ModularCurve_EichlerMass
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_ModularCurve_ssCountFormula_eq_genus

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single

open ModularCurve
namespace ModularCurve
theorem ssCountFormula_eq_genus {N q : ℕ} (hN : N ≠ 0) (hq : q.Prime)
    (hqN : ¬ q ∣ N) :
    ssCountFormula N q = genusFormula (N * q) - 2 * genusFormula N + 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ssCountFormula_eq_genus.solution
end ModularCurve

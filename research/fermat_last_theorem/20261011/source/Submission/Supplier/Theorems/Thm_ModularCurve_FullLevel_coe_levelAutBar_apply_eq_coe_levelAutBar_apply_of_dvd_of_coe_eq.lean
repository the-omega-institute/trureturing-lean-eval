import Submission.Supplier.Definitions.Def_ModularCurve_FullLevelJacobian
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_coe_levelAutBar_apply_of_dvd_of_coe_eq

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.FullLevel.coe_levelAutBar_apply_eq_coe_levelAutBar_apply_of_dvd_of_coe_eq
    (q : ℕ) [Fact q.Prime] (M' M'' : ℕ) (hM : M' ∣ M'') (hqM'' : ¬ q ∣ M'')
    (hLA : ModularCurve.FullLevel.LevelAutInputs q M') (hLA'' : ModularCurve.FullLevel.LevelAutInputs q M'')
    (ζ : ModularCurve.FullLevel.Idx q) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M'')
    (u : ModularCurve.FullLevel.fieldBar q M') (u'' : ModularCurve.FullLevel.fieldBar q M'')
    (hu : (u'' : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ))) :
    ((ModularCurve.FullLevel.levelAutBar q M'' ζ γ u'' : ModularCurve.FullLevel.fieldBar q M'') :
        LaurentSeries (AlgebraicClosure ℚ)) =
      ((ModularCurve.FullLevel.levelAutBar q M' ζ γ u : ModularCurve.FullLevel.fieldBar q M') :
        LaurentSeries (AlgebraicClosure ℚ)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_coe_levelAutBar_apply_of_dvd_of_coe_eq.solution

#print axioms ModularCurve.FullLevel.coe_levelAutBar_apply_eq_coe_levelAutBar_apply_of_dvd_of_coe_eq

import Submission.Supplier.Definitions.Def_ModularCurve_FullLevelJacobian
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_ModularCurve_FullLevel_levelAutBar_pow_inv_eq_levelAutBar_of_diag_conj

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel

open scoped MatrixGroups

theorem ModularCurve.FullLevel.levelAutBar_pow_inv_eq_levelAutBar_of_diag_conj (q : ℕ) [Fact q.Prime]
    (M' : ℕ) (hqM' : ¬ q ∣ M') (ζ : ModularCurve.FullLevel.Idx q) (d : (ZMod q)ˣ) (α α' : SL(2, ℤ))
    (hα : α ∈ CongruenceSubgroup.Gamma0 M') (hα' : α' ∈ CongruenceSubgroup.Gamma0 M')
    (h : !![(1 : ZMod q), 0; 0, (d : ZMod q)] * (α : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod q)
        = (α' : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod q) * !![(1 : ZMod q), 0; 0, (d : ZMod q)]) :
    ModularCurve.FullLevel.levelAutBar q M' (ζ.pow d⁻¹) α =
      ModularCurve.FullLevel.levelAutBar q M' ζ α' := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_levelAutBar_pow_inv_eq_levelAutBar_of_diag_conj.solution

#print axioms ModularCurve.FullLevel.levelAutBar_pow_inv_eq_levelAutBar_of_diag_conj

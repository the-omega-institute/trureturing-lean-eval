import Mathlib
import Submission.Supplier.Definitions.Def_FLTPrelim_Modularity
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_ModularForm_dvd_succ_mul_qCoeff_zero_of_dvd_qCoeff

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
attribute [-simp] ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

theorem ModularForm.dvd_succ_mul_qCoeff_zero_of_dvd_qCoeff (p : ℕ) [Fact p.Prime] (M : ℕ)
    (hM : Nat.Coprime M p) (E : ModularForm (CongruenceSubgroup.Gamma0 p) 2) (a : ℕ → ℤ)
    (ha : ∀ n : ℕ, (a n : ℂ) = ModularFormClass.qCoeff E n)
    (hdvd : ∀ n : ℕ, n ≠ 0 → (M : ℤ) ∣ a n) : (M : ℤ) ∣ ((p : ℤ) + 1) * a 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_dvd_succ_mul_qCoeff_zero_of_dvd_qCoeff.solution

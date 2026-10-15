import Mathlib
import Submission.Supplier.Definitions.Def_CuspForm_ModPForms
import Submission.Supplier.Theorems.Thm_CuspForm_qCoeffLinear_apply
import Submission.Supplier.P2M.Util

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
namespace P2MW.S_ModPForms_modPMod_eq_bot_of_neg

set_option autoImplicit false

open scoped MatrixGroups

theorem solution (N : ℕ) [NeZero N] (k : ℤ) (hk : k < 0) (F : Type) [Field F] :
    ModPForms.modPMod N k F = ⊥ := by
  unfold ModPForms.modPMod
  rw [Submodule.span_eq_bot]
  rintro φ ⟨f, a, ha, rfl⟩
  have hf : f = 0 := ModularForm.isZero_of_neg_weight hk f
  have h0 : ∀ n, ModularFormClass.qCoeff (f : UpperHalfPlane → ℂ) n = 0 := by
    intro n
    have e : (f : UpperHalfPlane → ℂ) = ((0 : CuspForm (CongruenceSubgroup.Gamma0 N) k) : UpperHalfPlane → ℂ) := by
      rw [hf, ModularForm.coe_zero, CuspForm.coe_zero]
    rw [e, ← CuspForm.qCoeffLinear_apply, map_zero]
  have han : ∀ n, a n = 0 := fun n => by
    have h := ha n
    rw [h0 n] at h
    exact_mod_cast h.symm
  ext n
  simp [PowerSeries.coeff_mk, han]

import Mathlib
import Submission.Supplier.Definitions.Def_CuspForm_ModPForms
import Submission.Supplier.P2M.Util

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
namespace P2MW.S_ModPForms_one_mem_modPMod_zero

set_option autoImplicit false

open UpperHalfPlane

theorem solution (N : ℕ) (F : Type) [Field F] :
    (1 : PowerSeries F) ∈ ModPForms.modPMod N 0 F := by
  unfold ModPForms.modPMod
  refine Submodule.subset_span ⟨(1 : ModularForm (CongruenceSubgroup.Gamma0 N) 0),
    fun n => if n = 0 then 1 else 0, fun n => ?_, ?_⟩
  · unfold ModularFormClass.qCoeff
    rw [ModularForm.qExpansion_one, PowerSeries.coeff_one]
    by_cases hn : n = 0 <;> simp [hn]
  · ext n
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_one]
    by_cases hn : n = 0 <;> simp [hn]

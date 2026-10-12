import Mathlib
import Submission.Supplier.Definitions.Def_ModularForm_AtkinLehnerDatum
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_ModularForm_AtkinLehnerDatum_exists_mem_Gamma0_alGL_mul_eq

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

open scoped MatrixGroups
theorem ModularForm.AtkinLehnerDatum.exists_mem_Gamma0_alGL_mul_eq {M q : ℕ} [NeZero M]
    (W : ModularForm.AtkinLehnerDatum M q) {g : SL(2, ℤ)} (hg : g ∈ CongruenceSubgroup.Gamma0 M) :
    ∃ δ : SL(2, ℤ), δ ∈ CongruenceSubgroup.Gamma0 M ∧
      W.alGL * Matrix.SpecialLinearGroup.mapGL ℝ g = Matrix.SpecialLinearGroup.mapGL ℝ δ * W.alGL := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_AtkinLehnerDatum_exists_mem_Gamma0_alGL_mul_eq.solution

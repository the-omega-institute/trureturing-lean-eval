import Submission.Supplier.Definitions.Def_CuspForm_PrimitiveFormGamma1
import Submission.Supplier.Definitions.Def_CuspForm_AdelicLiftGamma1
import Submission.Supplier.Definitions.Def_CuspForm_AdelicLift
import Submission.Supplier.Definitions.Def_CuspForm_Newforms
import Submission.Supplier.Definitions.Def_AutomorphicForm_CuspidalConstituent
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_CuspForm_IsAdelicLiftOfGamma1_exists_forall_norm_le

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ModularForm

theorem CuspForm.IsAdelicLiftOfGamma1.exists_forall_norm_le
    {M : ℕ} [NeZero M] {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    {Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hΦ : CuspForm.IsAdelicLiftOfGamma1 h Φ) :
    ∃ C : ℝ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ‖Φ g‖ ≤ C := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsAdelicLiftOfGamma1_exists_forall_norm_le.solution

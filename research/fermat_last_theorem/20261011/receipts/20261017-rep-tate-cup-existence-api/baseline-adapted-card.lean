import Mathlib
import Submission.Supplier.Definitions.Def_GroupCohomology_TateCohomology
import Submission.Supplier.Definitions.Def_GroupCohomology_TateSeam
import Submission.Supplier.Definitions.Def_GroupCohomology_TateShiftMaps
import Submission.Supplier.Definitions.Def_GroupCohomology_CochainCup
import Submission.Supplier.Definitions.Def_GroupCohomology_IsGradedCupProduct
import Submission.Supplier.Definitions.Def_GroupCohomology_IsTateCupProduct
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_Rep_exists_isTateCupProduct

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
attribute [-simp] Rep.coe_dimShiftDownObjMap_apply

set_option autoImplicit false
universe u
open CategoryTheory Rep MonoidalCategory
theorem Rep.exists_isTateCupProduct {k G : Type u} [CommRing k] [Group G] [Fintype G] :
    ∃ cup : Rep.TateCupFamily k G, Rep.IsTateCupProduct cup := by p2m_exact_reverting @_root_.P2MW.S_Rep_exists_isTateCupProduct.solution

import Mathlib
import Submission.Supplier.Definitions.Def_GroupCohomology_TateCohomology
import Submission.Supplier.Definitions.Def_GroupCohomology_TateDimensionShift
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_Rep_shortExact_map_tensorLeft_indBot

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false
universe u
open CategoryTheory Rep MonoidalCategory
theorem Rep.shortExact_map_tensorLeft_indBot {k G : Type u} [CommRing k] [Group G]
    {X : ShortComplex (Rep.{u} k G)} (A : Rep.{u} k G) (hAX : (X.map (MonoidalCategory.tensorLeft A)).ShortExact) :
    (X.map (MonoidalCategory.tensorLeft A.indBot)).ShortExact := by p2m_exact_reverting @_root_.P2MW.S_Rep_shortExact_map_tensorLeft_indBot.solution

import Mathlib
import Submission.Supplier.Definitions.Def_GroupCohomology_TateCohomology
import Submission.Supplier.Definitions.Def_GroupCohomology_TateSeam
import Submission.Supplier.Definitions.Def_GroupCohomology_TateDimensionShift
import Submission.Supplier.Definitions.Def_GroupCohomology_TateShiftMaps
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_Rep_tateDelta_comp_tateDelta_eq_neg

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
theorem Rep.tateDelta_comp_tateDelta_eq_neg {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {X Y : ShortComplex (Rep.{u} k G)}
    (hR₁ : (X.map (MonoidalCategory.tensorRight Y.X₁)).ShortExact)
    (hR₂ : (X.map (MonoidalCategory.tensorRight Y.X₂)).ShortExact)
    (hR₃ : (X.map (MonoidalCategory.tensorRight Y.X₃)).ShortExact)
    (hC₁ : (Y.map (MonoidalCategory.tensorLeft X.X₁)).ShortExact)
    (hC₂ : (Y.map (MonoidalCategory.tensorLeft X.X₂)).ShortExact)
    (hC₃ : (Y.map (MonoidalCategory.tensorLeft X.X₃)).ShortExact) (n : ℤ) :
    Rep.tateδ hR₃ n ≫ Rep.tateδ hC₁ (n + 1) = -(Rep.tateδ hC₃ n ≫ Rep.tateδ hR₁ (n + 1)) := by p2m_exact_reverting @_root_.P2MW.S_Rep_tateDelta_comp_tateDelta_eq_neg.solution

#print axioms Rep.tateDelta_comp_tateDelta_eq_neg

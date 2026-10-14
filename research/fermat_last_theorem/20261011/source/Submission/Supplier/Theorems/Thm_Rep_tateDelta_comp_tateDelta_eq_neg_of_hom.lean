import Mathlib
import Submission.Supplier.Definitions.Def_GroupCohomology_TateCohomology
import Submission.Supplier.Definitions.Def_GroupCohomology_TateSeam
import Submission.Supplier.Definitions.Def_GroupCohomology_TateDimensionShift
import Submission.Supplier.Definitions.Def_GroupCohomology_TateShiftMaps
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_Rep_tateDelta_comp_tateDelta_eq_neg_of_hom

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
theorem Rep.tateDelta_comp_tateDelta_eq_neg_of_hom {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {R₁ R₂ R₃ : ShortComplex (Rep.{u} k G)} (hR₁ : R₁.ShortExact) (hR₂ : R₂.ShortExact) (hR₃ : R₃.ShortExact)
    (v : R₁ ⟶ R₂) (w : R₂ ⟶ R₃)
    (h₁ : v.τ₁ ≫ w.τ₁ = 0) (h₂ : v.τ₂ ≫ w.τ₂ = 0) (h₃ : v.τ₃ ≫ w.τ₃ = 0)
    (hC₁ : (ShortComplex.mk v.τ₁ w.τ₁ h₁).ShortExact) (hC₂ : (ShortComplex.mk v.τ₂ w.τ₂ h₂).ShortExact)
    (hC₃ : (ShortComplex.mk v.τ₃ w.τ₃ h₃).ShortExact) (n : ℤ) :
    Rep.tateδ hR₃ n ≫ Rep.tateδ hC₁ (n + 1) = -(Rep.tateδ hC₃ n ≫ Rep.tateδ hR₁ (n + 1)) := by p2m_exact_reverting @_root_.P2MW.S_Rep_tateDelta_comp_tateDelta_eq_neg_of_hom.solution

import Mathlib
import Submission.Supplier.Definitions.Def_Deformations_ProartinianCat
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_Deformation_ProartinianCat_isCorepresentable_of_preservesLimits

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
attribute [-instance] Deformation.ProartinianCat.instFiniteResidueField Deformation.ProartinianCat.instCompactSpace
attribute [-simp] CategoryTheory.Functor.corepresentableByOfIsInitial_homEquiv_symm_apply CategoryTheory.Functor.representableByOfIsInitial_homEquiv_symm_apply CategoryTheory.Functor.corepresentableByOfIsInitial_homEquiv_apply CategoryTheory.Functor.representableByOfIsInitial_homEquiv_apply

open CategoryTheory IsLocalRing

universe u v
theorem Deformation.ProartinianCat.isCorepresentable_of_preservesLimits {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞]
  [Finite (IsLocalRing.ResidueField 𝓞)] (F : CategoryTheory.Functor (Deformation.ProartinianCat 𝓞) (Type u))
  [CategoryTheory.Limits.PreservesLimits F] : F.IsCorepresentable := by p2m_exact_reverting @_root_.P2MW.S_Deformation_ProartinianCat_isCorepresentable_of_preservesLimits.solution

#print axioms Deformation.ProartinianCat.isCorepresentable_of_preservesLimits

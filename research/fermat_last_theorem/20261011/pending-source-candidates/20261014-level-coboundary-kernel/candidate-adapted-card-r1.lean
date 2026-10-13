import Mathlib
import Submission.Supplier.Definitions.Def_GroupCohomology_ContinuousH2
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_groupCohomology_levelCoboundaries2_le_levelCocycles2

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

universe u
theorem groupCohomology.levelCoboundaries2_le_levelCocycles2 {k G : Type u} [CommRing k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (M : Rep k G)
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → M.ρ s m = m) :
    groupCohomology.levelCoboundaries₂ r M ≤ groupCohomology.levelCocycles₂ r M := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_levelCoboundaries2_le_levelCocycles2.solution

#print axioms groupCohomology.levelCoboundaries2_le_levelCocycles2

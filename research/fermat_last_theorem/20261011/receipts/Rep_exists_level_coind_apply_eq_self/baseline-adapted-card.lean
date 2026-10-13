import Mathlib
import Submission.Supplier.Definitions.Def_GroupCohomology_ContinuousH2
import Submission.Supplier.Definitions.Def_GroupCohomology_LevelSubgroup
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_Rep_exists_level_coind_apply_eq_self

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

universe u

open CategoryTheory
theorem Rep.exists_level_coind_apply_eq_self {k G : Type u} [CommRing k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Subgroup G) [S.FiniteIndex]
    (hS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup.comap r ≤ S)
    (N : Rep.{u} k S)
    (hsm : ∀ n : N, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : S, r s ∈ F.fixingSubgroup → N.ρ s n = n)
    (f : Rep.coind S.subtype N) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ u : G, r u ∈ F.fixingSubgroup → (Rep.coind S.subtype N).ρ u f = f := by p2m_exact_reverting @_root_.P2MW.S_Rep_exists_level_coind_apply_eq_self.solution

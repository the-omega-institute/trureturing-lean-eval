import Mathlib
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_AlgebraicGeometry_existsUnique_exists_comp_eq_of_isLocalHom_of_forall_ne

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.existsUnique_exists_comp_eq_of_isLocalHom_of_forall_ne
    {R A' : Type u} [CommRing R] [IsLocalRing R] [CommRing A'] [IsLocalRing A']
    (φ : R →+* A') [IsLocalHom φ]
    {N : Scheme.{u}} (g : N ⟶ Spec (CommRingCat.of R))
    (𝒰 : Scheme.OpenCover.{v} N)
    (hne : ∀ i k : 𝒰.I₀, i ≠ k → ∀ n ∈ Set.range (𝒰.f i).base ∩ Set.range (𝒰.f k).base,
      g.base n ≠ IsLocalRing.closedPoint R)
    (s : Spec (CommRingCat.of A') ⟶ N) (hs : s ≫ g = Spec.map (CommRingCat.ofHom φ)) :
    ∃! i : 𝒰.I₀, ∃ s' : Spec (CommRingCat.of A') ⟶ 𝒰.X i, s' ≫ 𝒰.f i = s := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_existsUnique_exists_comp_eq_of_isLocalHom_of_forall_ne.solution

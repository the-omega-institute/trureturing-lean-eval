import Mathlib
import Submission.Supplier.P2M.Util

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
namespace P2MW.S_AlgebraicGeometry_comp_hom_eq_hom_comp_of_unique_isClosedImmersion_section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {X Y : Scheme.{u}} (π : X ⟶ Y) (c : Y ⟶ X) [IsClosedImmersion c] (hcπ : c ≫ π = 𝟙 Y)
    (huniq : ∀ s : Y ⟶ X, IsClosedImmersion s → s ≫ π = 𝟙 Y → s = c)
    (φ : X ≅ X) (φ₀ : Y ≅ Y) (hπ : φ.hom ≫ π = π ≫ φ₀.hom) :
    c ≫ φ.hom = φ₀.hom ≫ c := by

  have hs : IsClosedImmersion (φ₀.inv ≫ c ≫ φ.hom) := inferInstance
  have hsec : (φ₀.inv ≫ c ≫ φ.hom) ≫ π = 𝟙 Y := by
    rw [Category.assoc, Category.assoc, hπ, ← Category.assoc c, hcπ, Category.id_comp, Iso.inv_hom_id]
  have key := huniq _ hs hsec

  calc c ≫ φ.hom = φ₀.hom ≫ (φ₀.inv ≫ c ≫ φ.hom) := by rw [Iso.hom_inv_id_assoc]
    _ = φ₀.hom ≫ c := by rw [key]

#print axioms solution

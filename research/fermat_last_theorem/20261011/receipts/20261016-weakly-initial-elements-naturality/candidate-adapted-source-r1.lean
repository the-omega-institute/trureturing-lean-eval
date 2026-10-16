import Mathlib
import Submission.Supplier.Definitions.Def_Deformations_ConjQuotSubfunctor
import Submission.Supplier.P2M.Util

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
namespace P2MW.S_Deformation_exists_weaklyInitial_elements_conjQuotSubfunctor

p2m_open "CategoryTheory P2MW.S_Deformation_exists_weaklyInitial_elements_conjQuotSubfunctor.CategoryTheory"

namespace CategoryTheory
p2m_export "CategoryTheory" "NatTrans.naturality_apply Category NatTrans.mapElements Subfunctor"
namespace CategoryOfElements
p2m_export "CategoryTheory.NatTrans" "mapElements"
namespace SolAux
p2m_open "CategoryTheory.CategoryOfElements CategoryTheory"

universe w v u
variable {C : Type u} [Category.{v} C] {F₁ F₂ : C ⥤ Type w}

theorem map_obj_weaklyInitial (α : F₁ ⟶ F₂) (hα : ∀ X, Function.Surjective (α.app X))
    {T : F₁.Elements} (hT : ∀ X, Nonempty (T ⟶ X)) (Y : F₂.Elements) :
    Nonempty ((NatTrans.mapElements α).obj T ⟶ Y) := by
  obtain ⟨x, hx⟩ := hα Y.obj Y.val
  obtain ⟨f⟩ := hT (F₁.elementsMk Y.obj x)
  refine ⟨⟨f.hom, ?_⟩⟩
  show F₂.map f.hom (α.app T.obj T.val) = Y.val
  rw [← NatTrans.naturality_apply, f.map_val, hx]

end CategoryTheory.CategoryOfElements.SolAux

universe u

theorem solution (n : Type) [Fintype n] [DecidableEq n] {G : Type u} [Group G]
    [TopologicalSpace G] {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞]
    {F : CategoryTheory.Subfunctor (Deformation.repnFunctor n G 𝓞)} (T : F.toFunctor.Elements)
    (hT : ∀ (X : F.toFunctor.Elements), Nonempty (T ⟶ X)) :
    ∃ T', ∀ (X : (Deformation.conjQuotSubfunctor n F).toFunctor.Elements), Nonempty (T' ⟶ X) :=
  ⟨(NatTrans.mapElements (Deformation.condLiftToDeformation n F)).obj T,
    CategoryTheory.CategoryOfElements.SolAux.map_obj_weaklyInitial (Deformation.condLiftToDeformation n F)
      (Deformation.condLiftToDeformation_surjective n F) hT⟩

#print axioms solution

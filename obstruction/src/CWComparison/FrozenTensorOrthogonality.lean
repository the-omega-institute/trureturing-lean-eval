/-
Selected immutable proved supplier, Apache 2.0.
Source: root-verified derived-orthogonality checkpoint, DerivedCellOrthogonality.lean.
Only unrelated cellular proofs omitted; inclusion locality reuses the already
compiled identical comparison proof. Exact mate and single-complex bridges retained.
-/
import CWComparison.FrozenExactMates
import CWComparison.DerivedTensorLocality

noncomputable section
open CategoryTheory Limits MonoidalCategory MonoidalClosed HomologicalComplex
open Pretriangulated

namespace LightCondensed.Solid

private theorem precomp_bijective_conjugate
    {C : Type*} [Category* C] {X X' Y : C} (e : X ≅ X')
    (f : X ⟶ X) (f' : X' ⟶ X') (he : f ≫ e.hom = e.hom ≫ f')
    (hf : Function.Bijective (fun (g : X ⟶ Y) => f ≫ g)) :
    Function.Bijective (fun (g : X' ⟶ Y) => f' ≫ g) := by
  constructor
  · intro u v huv
    apply (cancel_epi e.hom).1
    apply hf.injective
    change f ≫ (e.hom ≫ u) = f ≫ (e.hom ≫ v)
    calc
      f ≫ e.hom ≫ u = e.hom ≫ f' ≫ u := by rw [← Category.assoc, he, Category.assoc]
      _ = e.hom ≫ f' ≫ v := congrArg (e.hom ≫ ·) huv
      _ = f ≫ e.hom ≫ v := by rw [← Category.assoc, ← he, Category.assoc]
  · intro u
    obtain ⟨v, hv⟩ := hf.surjective (e.hom ≫ u)
    refine ⟨e.inv ≫ v, ?_⟩
    apply (cancel_epi e.hom).1
    rw [← Category.assoc, ← he, Category.assoc, e.hom_inv_id_assoc]
    exact hv

/-- The defining action on tensoring with the protected P, in all degrees. -/
def solidTensorEndomorphism : tensorLeft P ⟶ tensorLeft P :=
  (tensoringLeft LightCondAb).map oneMinusShift

/-- Its genuine derived natural transformation; tensoring with P is exact. -/
def solidDerivedTensorEndomorphism :
    (tensorLeft P).mapDerivedCategory ⟶ (tensorLeft P).mapDerivedCategory :=
  solidTensorEndomorphism.mapDerivedCategory

/-- Exact original defining internal-Hom action; immutable supplier definition. -/
def solidDerivedEndomorphism :
    (ihom P).mapDerivedCategory ⟶ (ihom P).mapDerivedCategory :=
  (MonoidalClosed.pre oneMinusShift).mapDerivedCategory

/-- Reuse the already compiled identical inclusion-locality theorem. -/
theorem solidDerivedEndomorphism_derivedInclusion_isIso (Y : DSolid) :
    IsIso (solidDerivedEndomorphism.app (derivedInclusion.obj Y)) :=
  CWComparison.derivedPreP_solid_isIso Y

set_option backward.isDefEq.respectTransparency false in
/-- The defining map with an arbitrary derived tensor parameter induces
a bijection on derived maps into any object with vanishing locality defect.
Both the source and target may be unbounded. -/
theorem solidDerivedTensor_precomp_bijective
    (X Y : DLightCondAb) [IsIso (solidDerivedEndomorphism.app Y)] :
    Function.Bijective (fun (g : (tensorLeft P).mapDerivedCategory.obj X ⟶ Y) =>
      solidDerivedTensorEndomorphism.app X ≫ g) := by
  let adj := CWSolid.exactAdjunctionDerived (ihom.adjunction P)
  let e := adj.homEquiv X Y
  have mate (g : (tensorLeft P).mapDerivedCategory.obj X ⟶ Y) :
      e (solidDerivedTensorEndomorphism.app X ≫ g) =
        e g ≫ solidDerivedEndomorphism.app Y := by
    exact CWSolid.exactAdjunctionDerived_homEquiv_mate (ihom.adjunction P)
      solidTensorEndomorphism (MonoidalClosed.pre oneMinusShift)
      (fun B => (MonoidalClosed.coev_app_comp_pre_app B oneMinusShift).symm) X Y g
  constructor
  · intro f g h
    apply e.injective
    apply (cancel_mono (solidDerivedEndomorphism.app Y)).1
    rw [← mate, ← mate]
    exact congrArg e h
  · intro g
    let f := e.symm (e g ≫ inv (solidDerivedEndomorphism.app Y))
    refine ⟨f, e.injective ?_⟩
    rw [mate]
    simp [f]

set_option backward.isDefEq.respectTransparency false in
/-- The same bijection for the actual degreewise map on any unbounded
complex, not just for a single free generator. -/
theorem solidTensorComplex_precomp_bijective
    (K : CochainComplex LightCondAb ℤ) (Y : DLightCondAb)
    [IsIso (solidDerivedEndomorphism.app Y)] :
    Function.Bijective (fun (g : DerivedCategory.Q.obj
      ((tensorLeft P).mapHomologicalComplex (.up ℤ) |>.obj K) ⟶ Y) =>
        DerivedCategory.Q.map ((solidTensorEndomorphism.mapHomologicalComplex (.up ℤ)).app K) ≫ g) := by
  let e := (tensorLeft P).mapDerivedCategoryFactors.app K
  let f := DerivedCategory.Q.map
    ((solidTensorEndomorphism.mapHomologicalComplex (.up ℤ)).app K)
  have he : solidDerivedTensorEndomorphism.app (DerivedCategory.Q.obj K) ≫ e.hom =
      e.hom ≫ f := by
    rw [solidDerivedTensorEndomorphism, NatTrans.mapDerivedCategory_app_Q_obj]
    simp [e, f, Category.assoc]
  have hb := solidDerivedTensor_precomp_bijective (DerivedCategory.Q.obj K) Y
  exact precomp_bijective_conjugate e _ f he hb

set_option backward.isDefEq.respectTransparency false in
/-- The actual defining map placed in any integer degree is invisible to
maps into derived-local targets. No projectivity of the tensor parameter
and no derived solidification adjunction is used. -/
theorem solidTensorSingle_precomp_bijective
    (B : LightCondAb) (n : ℤ) (Y : DLightCondAb)
    [IsIso (solidDerivedEndomorphism.app Y)] :
    Function.Bijective (fun (g : DerivedCategory.Q.obj
      ((single LightCondAb (.up ℤ) n).obj (P ⊗ B)) ⟶ Y) =>
        DerivedCategory.Q.map ((single LightCondAb (.up ℤ) n).map (oneMinusShift ▷ B)) ≫ g) := by
  let K := (single LightCondAb (.up ℤ) n).obj B
  let ec := (singleMapHomologicalComplex (tensorLeft P) (.up ℤ) n).app B
  let f := (solidTensorEndomorphism.mapHomologicalComplex (.up ℤ)).app K
  let f' := (single LightCondAb (.up ℤ) n).map (oneMinusShift ▷ B)
  have h : f ≫ ec.hom = ec.hom ≫ f' := by
    have hh := natTransMapHomologicalComplex_app_single_obj
      solidTensorEndomorphism (.up ℤ) n B
    change f = ec.hom ≫ f' ≫ ec.inv at hh
    rw [hh]
    simp [Category.assoc]
  exact precomp_bijective_conjugate (DerivedCategory.Q.mapIso ec)
    (DerivedCategory.Q.map f) (DerivedCategory.Q.map f')
    (by simpa only [Functor.mapIso_hom, ← Functor.map_comp] using congrArg DerivedCategory.Q.map h)
    (solidTensorComplex_precomp_bijective K Y)


end LightCondensed.Solid

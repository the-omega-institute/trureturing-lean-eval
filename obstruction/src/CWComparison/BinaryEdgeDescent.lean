/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in src/licenses/LICENSE.LeanCondensed.

Actual sheaf descent for shrinking free interval differences. The geometric
construction follows the root's frozen binary-subdivision advisory; none of its
claims are imported as a proof or assumed as an acyclicity hypothesis.
-/
import CWComparison.BinaryEdgeRelation
import CWComparison.BinaryEdgeChildren
import CWComparison.FreeCoverPresentation

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits LightCondensed LightCondensed.Solid LightProfinite OnePoint TopologicalSpace

namespace CWComparison

local instance : MetrizableSpace (TopCat.of (binaryEdgeInfinity × binaryEdgeInfinity)) :=
  by
    letI : MetricSpace binaryEdgeSpace := metrizableSpaceMetric _
    infer_instance

/-- The actual free functors agree along the proved light-profinite/topological
comparison. No free or solid object is replaced by an alias. -/
def freeProfiniteTopNatIso :
    lightProfiniteToLightCondSet ⋙ free ℤ ≅ toTopCat ⋙ freeLightCondAbOfTopFunctor :=
  Functor.isoWhiskerRight lightProfiniteToLightCondSetIsoTopCatToLightCondSet (free ℤ)

instance binaryEdgeSpace_nonempty : Nonempty binaryEdgeSpace := ⟨binaryEdgePoint 0⟩

instance binaryEdgeInfinity_nonempty : Nonempty binaryEdgeInfinity := by
  obtain ⟨p, hp⟩ := binaryEdgeProjection_surjective ∞
  exact ⟨⟨p, hp⟩⟩

/-- A finite light-profinite cover of the two genuine closed relation pieces. -/
abbrev binaryEdgeRelationCoverSource : LightProfinite :=
  CompHausLike.finiteCoproduct (fun _ : Bool => cantorProfinite)

def binaryEdgeRelationPiece : Bool → C(cantorProfinite, binaryEdgeRelation)
  | true => binaryEdgeRelationDiagonal.comp (compactMetrizableCover (TopCat.of binaryEdgeSpace))
  | false => binaryEdgeRelationInfinity.comp
      (compactMetrizableCover (TopCat.of (binaryEdgeInfinity × binaryEdgeInfinity)))

def binaryEdgeRelationProfiniteCover :
    C(binaryEdgeRelationCoverSource, binaryEdgeRelation) where
  toFun p := binaryEdgeRelationPiece p.1 p.2
  continuous_toFun := continuous_sigma (fun b => (binaryEdgeRelationPiece b).continuous)

theorem binaryEdgeRelationProfiniteCover_surjective :
    Function.Surjective binaryEdgeRelationProfiniteCover := by
  intro r
  obtain ⟨s, hs⟩ := binaryEdgeRelationCover_surjective r
  cases s with
  | inl p =>
    obtain ⟨c, hc⟩ := compactMetrizableCover_surjective (TopCat.of binaryEdgeSpace) p
    exact ⟨⟨true, c⟩, by simpa [binaryEdgeRelationProfiniteCover, binaryEdgeRelationPiece, binaryEdgeRelationCover, hc] using hs⟩
  | inr p =>
    obtain ⟨c, hc⟩ := compactMetrizableCover_surjective
      (TopCat.of (binaryEdgeInfinity × binaryEdgeInfinity)) p
    exact ⟨⟨false, c⟩, by simpa [binaryEdgeRelationProfiniteCover, binaryEdgeRelationPiece, binaryEdgeRelationCover, hc] using hs⟩

/-- The free difference is formed using the protected topological free functor. -/
def binaryEdgeFreeDifference : freeLightCondAbOfTopFunctor.obj (TopCat.of binaryEdgeSpace) ⟶
    freeLightCondAbOfTopFunctor.obj (TopCat.of unitInterval) :=
  freeLightCondAbOfTopFunctor.map (TopCat.ofHom binaryEdgeEnd) -
    freeLightCondAbOfTopFunctor.map (TopCat.ofHom binaryEdgeStart)

abbrev binaryEdgeProjectionTop : TopCat.of binaryEdgeSpace ⟶ TopCat.of (OnePoint ℕ) :=
  TopCat.ofHom binaryEdgeProjection

abbrev binaryEdgeRelationFst : TopCat.of binaryEdgeRelation ⟶ TopCat.of binaryEdgeSpace :=
  (TopCat.pullbackCone binaryEdgeProjectionTop binaryEdgeProjectionTop).fst

abbrev binaryEdgeRelationSnd : TopCat.of binaryEdgeRelation ⟶ TopCat.of binaryEdgeSpace :=
  (TopCat.pullbackCone binaryEdgeProjectionTop binaryEdgeProjectionTop).snd

/-- Checking the free relation on both genuine covering pieces. -/
private theorem binaryEdge_relation_piece (b : Bool) :
    freeLightCondAbOfTopFunctor.map (TopCat.ofHom (binaryEdgeRelationPiece b)) ≫
      freeLightCondAbOfTopFunctor.map binaryEdgeRelationFst ≫ binaryEdgeFreeDifference =
    freeLightCondAbOfTopFunctor.map (TopCat.ofHom (binaryEdgeRelationPiece b)) ≫
      freeLightCondAbOfTopFunctor.map binaryEdgeRelationSnd ≫ binaryEdgeFreeDifference := by
  cases b
  · simp only [binaryEdgeFreeDifference]
    simp only [Preadditive.comp_sub, ← Functor.map_comp_assoc, ← Functor.map_comp]
    have h₁ : TopCat.ofHom (binaryEdgeRelationPiece false) ≫ binaryEdgeRelationFst ≫
        TopCat.ofHom binaryEdgeEnd =
      TopCat.ofHom (binaryEdgeRelationPiece false) ≫ binaryEdgeRelationFst ≫
        TopCat.ofHom binaryEdgeStart := by
      ext c
      exact congrArg Subtype.val ((binaryEdge_infty_fiber _
        ((compactMetrizableCover (TopCat.of (binaryEdgeInfinity × binaryEdgeInfinity)) c).1.property)).symm)
    have h₂ : TopCat.ofHom (binaryEdgeRelationPiece false) ≫ binaryEdgeRelationSnd ≫
        TopCat.ofHom binaryEdgeEnd =
      TopCat.ofHom (binaryEdgeRelationPiece false) ≫ binaryEdgeRelationSnd ≫
        TopCat.ofHom binaryEdgeStart := by
      ext c
      exact congrArg Subtype.val ((binaryEdge_infty_fiber _
        ((compactMetrizableCover (TopCat.of (binaryEdgeInfinity × binaryEdgeInfinity)) c).2.property)).symm)
    rw [h₁, h₂]
    simp
  · have h : TopCat.ofHom (binaryEdgeRelationPiece true) ≫ binaryEdgeRelationFst =
        TopCat.ofHom (binaryEdgeRelationPiece true) ≫ binaryEdgeRelationSnd := by ext c <;> rfl
    rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, h]

/-- This is equality on the full kernel pair, proved by a genuine free sheaf
cover and its preserved finite coproduct, not by ordinary points. -/
theorem binaryEdgeFreeDifference_relation :
    freeLightCondAbOfTopFunctor.map binaryEdgeRelationFst ≫ binaryEdgeFreeDifference =
      freeLightCondAbOfTopFunctor.map binaryEdgeRelationSnd ≫ binaryEdgeFreeDifference := by
  let c := TopCat.ofHom binaryEdgeRelationProfiniteCover
  have : Epi (freeLightCondAbOfTopFunctor.map c) :=
    profiniteCover_free_epi (T := binaryEdgeRelationCoverSource)
      (X := TopCat.of binaryEdgeRelation) _ binaryEdgeRelationProfiniteCover_surjective
  apply (cancel_epi (freeLightCondAbOfTopFunctor.map c)).1
  let F := toTopCat ⋙ freeLightCondAbOfTopFunctor
  letI : PreservesColimitsOfShape (Discrete Bool) F :=
    preservesColimitsOfShape_of_natIso freeProfiniteTopNatIso
  apply (isColimitOfPreserves F
    (CompHausLike.finiteCoproduct.isColimit (fun _ : Bool => cantorProfinite))).hom_ext
  intro ⟨b⟩
  change freeLightCondAbOfTopFunctor.map
    (toTopCat.map (CompHausLike.finiteCoproduct.ι (fun _ : Bool => cantorProfinite) b)) ≫
      freeLightCondAbOfTopFunctor.map c ≫
        (freeLightCondAbOfTopFunctor.map binaryEdgeRelationFst ≫ binaryEdgeFreeDifference) = _
  change freeLightCondAbOfTopFunctor.map
      (toTopCat.map (CompHausLike.finiteCoproduct.ι (fun _ : Bool => cantorProfinite) b)) ≫
        (freeLightCondAbOfTopFunctor.map c ≫
          freeLightCondAbOfTopFunctor.map binaryEdgeRelationFst ≫ binaryEdgeFreeDifference) =
    freeLightCondAbOfTopFunctor.map
      (toTopCat.map (CompHausLike.finiteCoproduct.ι (fun _ : Bool => cantorProfinite) b)) ≫
        (freeLightCondAbOfTopFunctor.map c ≫
          freeLightCondAbOfTopFunctor.map binaryEdgeRelationSnd ≫ binaryEdgeFreeDifference)
  have he : toTopCat.map (CompHausLike.finiteCoproduct.ι
      (fun _ : Bool => cantorProfinite) b) ≫ c = TopCat.ofHom (binaryEdgeRelationPiece b) := rfl
  have hι : freeLightCondAbOfTopFunctor.map
      (toTopCat.map (CompHausLike.finiteCoproduct.ι (fun _ : Bool => cantorProfinite) b)) ≫
      freeLightCondAbOfTopFunctor.map c =
        freeLightCondAbOfTopFunctor.map (TopCat.ofHom (binaryEdgeRelationPiece b)) :=
    (freeLightCondAbOfTopFunctor.map_comp _ _).symm.trans
      (congrArg freeLightCondAbOfTopFunctor.map he)
  have h₁ := congrArg (fun k => k ≫ freeLightCondAbOfTopFunctor.map binaryEdgeRelationFst ≫
    binaryEdgeFreeDifference) hι
  have h₂ := congrArg (fun k => k ≫ freeLightCondAbOfTopFunctor.map binaryEdgeRelationSnd ≫
    binaryEdgeFreeDifference) hι
  simpa only [Category.assoc] using h₁.trans ((binaryEdge_relation_piece b).trans h₂.symm)


/-- Descent is the effective epimorphism coequalizer of the actual projection. -/
def binaryEdgeFreeCoforkIsColimit : IsColimit
    (Cofork.ofπ (freeLightCondAbOfTopFunctor.map binaryEdgeProjectionTop)
      (show freeLightCondAbOfTopFunctor.map binaryEdgeRelationFst ≫
          freeLightCondAbOfTopFunctor.map binaryEdgeProjectionTop =
        freeLightCondAbOfTopFunctor.map binaryEdgeRelationSnd ≫
          freeLightCondAbOfTopFunctor.map binaryEdgeProjectionTop by
        rw [← Functor.map_comp, ← Functor.map_comp]
        exact congrArg freeLightCondAbOfTopFunctor.map
          (TopCat.pullbackCone binaryEdgeProjectionTop binaryEdgeProjectionTop).condition)) := by
  letI : topCatToLightCondSet.IsRightAdjoint := LightCondSet.topCatAdjunction.isRightAdjoint
  letI : Epi (topCatToLightCondSet.map binaryEdgeProjectionTop) := binaryEdgeProjection_condensed_epi
  letI : EffectiveEpi (topCatToLightCondSet.map binaryEdgeProjectionTop) :=
    (regularEpiOfEpi _).effectiveEpi
  let c := TopCat.pullbackCone binaryEdgeProjectionTop binaryEdgeProjectionTop
  let c' := PullbackCone.mk (topCatToLightCondSet.map c.fst) (topCatToLightCondSet.map c.snd)
    (by rw [← Functor.map_comp, ← Functor.map_comp]; exact congrArg _ c.condition)
  have hc' : IsLimit c' := isLimitPullbackConeMapOfIsLimit topCatToLightCondSet c.condition
    (TopCat.pullbackConeIsLimit binaryEdgeProjectionTop binaryEdgeProjectionTop)
  exact isColimitCoforkMapOfIsColimit (free ℤ) c'.condition
    (isColimitCoforkOfEffectiveEpi (topCatToLightCondSet.map binaryEdgeProjectionTop) c' hc')

/-- The actual condensed null sequence of free edge differences. -/
def binaryEdgeFreeSequence : freeLightCondAbOfTopFunctor.obj (TopCat.of (OnePoint ℕ)) ⟶
    freeLightCondAbOfTopFunctor.obj (TopCat.of unitInterval) :=
  binaryEdgeFreeCoforkIsColimit.desc
    (Cofork.ofπ binaryEdgeFreeDifference binaryEdgeFreeDifference_relation)

@[reassoc (attr := simp)] theorem binaryEdgeFreeSequence_fac :
    freeLightCondAbOfTopFunctor.map binaryEdgeProjectionTop ≫ binaryEdgeFreeSequence =
      binaryEdgeFreeDifference := binaryEdgeFreeCoforkIsColimit.fac _ WalkingParallelPair.one

end CWComparison

namespace CWComparison

open CategoryTheory Limits LightCondensed LightCondensed.Solid LightProfinite OnePoint

/-- The infinity value is killed as an actual free morphism, using a lifted
infinity section of the genuine epimorphic parameter. -/
theorem binaryEdgeFreeSequence_infty :
    freeLightCondAbOfTopFunctor.map (toTopCat.map ι) ≫ binaryEdgeFreeSequence = 0 := by
  obtain ⟨p, hp⟩ := binaryEdgeProjection_surjective ∞
  let j : (LightProfinite.of PUnit).toTop ⟶ TopCat.of binaryEdgeSpace :=
    TopCat.ofHom ⟨fun _ => p, continuous_const⟩
  have hq : j ≫ binaryEdgeProjectionTop = toTopCat.map ι := by ext x; exact hp
  rw [← hq, Functor.map_comp, Category.assoc, binaryEdgeFreeSequence_fac]
  simp only [binaryEdgeFreeDifference]
  rw [Preadditive.comp_sub, ← Functor.map_comp, ← Functor.map_comp]
  have h : j ≫ TopCat.ofHom binaryEdgeEnd = j ≫ TopCat.ofHom binaryEdgeStart := by
    ext x
    exact congrArg Subtype.val (binaryEdge_infty_fiber p hp).symm
  erw [h]
  simp only [Functor.comp_map, ← Functor.map_comp, sub_self]

/-- Descending the actual null sequence through the exact protected quotient. -/
def binaryEdgePMap : P ⟶ freeLightCondAbOfTopFunctor.obj (TopCat.of unitInterval) :=
  P_homMk _ (freeProfiniteTopNatIso.hom.app (ℕ∪{∞}) ≫ binaryEdgeFreeSequence) (by
    change (lightProfiniteToLightCondSet ⋙ free ℤ).map ι ≫
      (freeProfiniteTopNatIso.hom.app _ ≫ binaryEdgeFreeSequence) = 0
    rw [← Category.assoc, freeProfiniteTopNatIso.hom.naturality, Category.assoc]
    change _ ≫ (freeLightCondAbOfTopFunctor.map (toTopCat.map ι) ≫ binaryEdgeFreeSequence) = 0
    rw [binaryEdgeFreeSequence_infty, HasZeroMorphisms.comp_zero])

@[reassoc (attr := simp)] theorem binaryEdgePMap_fac :
    P_proj ≫ binaryEdgePMap =
      freeProfiniteTopNatIso.hom.app (ℕ∪{∞}) ≫ binaryEdgeFreeSequence := by
  simp [binaryEdgePMap, P_homMk, P_proj]

/-- The root edge evaluates to the exact free endpoint difference. -/
theorem binaryEdgePMap_root : Pfinite 0 ≫ binaryEdgePMap =
    freeProfiniteTopNatIso.hom.app (LightProfinite.of PUnit) ≫
      (freeLightCondAbOfTopFunctor.map
          (TopCat.ofHom (X := (LightProfinite.of PUnit).toTop)
            (Y := TopCat.of unitInterval) (ContinuousMap.const _ 1)) -
        freeLightCondAbOfTopFunctor.map
          (TopCat.ofHom (X := (LightProfinite.of PUnit).toTop)
            (Y := TopCat.of unitInterval) (ContinuousMap.const _ 0))) := by
  let j : (LightProfinite.of PUnit).toTop ⟶ TopCat.of binaryEdgeSpace :=
    TopCat.ofHom ⟨fun _ => binaryEdgePoint 0, continuous_const⟩
  dsimp [Pfinite]
  erw [Category.assoc, binaryEdgePMap_fac, ← Category.assoc,
    freeProfiniteTopNatIso.hom.naturality, Category.assoc]
  have hq : toTopCat.map
      (ConcreteCategory.ofHom (X := LightProfinite.of PUnit) (Y := ℕ∪{∞})
        ⟨fun _ => OnePoint.some 0, continuous_const⟩) = j ≫ binaryEdgeProjectionTop := rfl
  change freeProfiniteTopNatIso.hom.app (LightProfinite.of PUnit) ≫
      freeLightCondAbOfTopFunctor.map (toTopCat.map
        (ConcreteCategory.ofHom (X := LightProfinite.of PUnit) (Y := ℕ∪{∞})
          ⟨fun _ => OnePoint.some 0, continuous_const⟩)) ≫ binaryEdgeFreeSequence =
    freeProfiniteTopNatIso.hom.app (LightProfinite.of PUnit) ≫
      (freeLightCondAbOfTopFunctor.map (TopCat.ofHom
        (X := (LightProfinite.of PUnit).toTop) (Y := TopCat.of unitInterval)
        (ContinuousMap.const _ 1)) -
      freeLightCondAbOfTopFunctor.map (TopCat.ofHom
        (X := (LightProfinite.of PUnit).toTop) (Y := TopCat.of unitInterval)
        (ContinuousMap.const _ 0)))
  erw [hq, Functor.map_comp, Category.assoc, binaryEdgeFreeSequence_fac]
  simp only [binaryEdgeFreeDifference]
  simp only [Preadditive.comp_sub, ← Functor.map_comp, ← Category.assoc]
  congr 2
  · congr 1
    ext x
    simp [j, binaryEdgePoint, binaryEdgeEnd, binaryEdgeB]
  · congr 1
    ext x
    simp [j, binaryEdgePoint, binaryEdgeStart, binaryEdgeA]

end CWComparison

namespace CWComparison

open CategoryTheory Limits LightCondensed LightCondensed.Solid LightProfinite OnePoint

/-- The left and right free edge differences telescope as actual morphisms. -/
theorem binaryEdgeFreeDifference_subdivision :
    freeLightCondAbOfTopFunctor.map (TopCat.ofHom binaryEdgeLeftChild) ≫ binaryEdgeFreeDifference +
      freeLightCondAbOfTopFunctor.map (TopCat.ofHom binaryEdgeRightChild) ≫ binaryEdgeFreeDifference =
        binaryEdgeFreeDifference := by
  simp only [binaryEdgeFreeDifference]
  simp only [Preadditive.comp_sub, ← Functor.map_comp]
  change
    (freeLightCondAbOfTopFunctor.map (TopCat.ofHom (binaryEdgeEnd.comp binaryEdgeLeftChild)) -
      freeLightCondAbOfTopFunctor.map (TopCat.ofHom (binaryEdgeStart.comp binaryEdgeLeftChild))) +
    (freeLightCondAbOfTopFunctor.map (TopCat.ofHom (binaryEdgeEnd.comp binaryEdgeRightChild)) -
      freeLightCondAbOfTopFunctor.map (TopCat.ofHom (binaryEdgeStart.comp binaryEdgeRightChild))) = _
  rw [binaryEdgeLeftChild_start, binaryEdgeRightChild_end, binaryEdgeChildren_midpoint]
  simp only [Functor.comp_map]
  abel

/-- Subdivision is preserved by the genuine effective-epimorphism descent. -/
theorem binaryEdgeFreeSequence_subdivision :
    (freeLightCondAbOfTopFunctor.map (toTopCat.map binaryLeft) +
      freeLightCondAbOfTopFunctor.map (toTopCat.map binaryRight)) ≫
        binaryEdgeFreeSequence = binaryEdgeFreeSequence := by
  letI : Epi (topCatToLightCondSet.map binaryEdgeProjectionTop) := binaryEdgeProjection_condensed_epi
  letI : Epi (freeLightCondAbOfTopFunctor.map binaryEdgeProjectionTop) := (free ℤ).map_epi _
  apply (cancel_epi (freeLightCondAbOfTopFunctor.map binaryEdgeProjectionTop)).1
  have hl : binaryEdgeProjectionTop ≫ toTopCat.map binaryLeft =
      TopCat.ofHom binaryEdgeLeftChild ≫ binaryEdgeProjectionTop := rfl
  have hr : binaryEdgeProjectionTop ≫ toTopCat.map binaryRight =
      TopCat.ofHom binaryEdgeRightChild ≫ binaryEdgeProjectionTop := rfl
  simp only [Preadditive.add_comp, Preadditive.comp_add]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, hl, hr]
  simp only [Functor.map_comp, Category.assoc, binaryEdgeFreeSequence_fac]
  exact binaryEdgeFreeDifference_subdivision

/-- The descended sequence satisfies the genuine binary relation on the
protected P, together with the protected oneMinusShift identities. -/
theorem binaryEdgePMap_subdivision :
    (PbinaryLeft + PbinaryRight) ≫ binaryEdgePMap = binaryEdgePMap := by
  letI : Epi P_proj := inferInstanceAs (Epi (cokernel.π P_map))
  apply (cancel_epi P_proj).1
  simp only [Preadditive.add_comp, Preadditive.comp_add]
  dsimp [PbinaryLeft, PbinaryRight]
  simp only [P_proj_sequencePMap_assoc, Category.assoc, binaryEdgePMap_fac]
  have h₁ := freeProfiniteTopNatIso.hom.naturality binaryLeft
  have h₂ := freeProfiniteTopNatIso.hom.naturality binaryRight
  change (lightProfiniteToLightCondSet ⋙ free ℤ).map binaryLeft ≫
    freeProfiniteTopNatIso.hom.app (ℕ∪{∞}) =
    freeProfiniteTopNatIso.hom.app (ℕ∪{∞}) ≫
      freeLightCondAbOfTopFunctor.map (toTopCat.map binaryLeft) at h₁
  change (lightProfiniteToLightCondSet ⋙ free ℤ).map binaryRight ≫
    freeProfiniteTopNatIso.hom.app (ℕ∪{∞}) =
    freeProfiniteTopNatIso.hom.app (ℕ∪{∞}) ≫
      freeLightCondAbOfTopFunctor.map (toTopCat.map binaryRight) at h₂
  change ((lightProfiniteToLightCondSet ⋙ free ℤ).map binaryLeft ≫
      freeProfiniteTopNatIso.hom.app (ℕ∪{∞})) ≫ binaryEdgeFreeSequence +
    ((lightProfiniteToLightCondSet ⋙ free ℤ).map binaryRight ≫
      freeProfiniteTopNatIso.hom.app (ℕ∪{∞})) ≫ binaryEdgeFreeSequence = _
  rw [h₁, h₂]
  simp only [Category.assoc]
  rw [← Preadditive.comp_add, ← Preadditive.add_comp, binaryEdgeFreeSequence_subdivision]


end CWComparison

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in src/licenses/LICENSE.LeanCondensed.
-/
import CWComparison.BinaryEdgeSpace

noncomputable section
open CategoryTheory Limits Topology OnePoint TopologicalSpace

namespace CWComparison

/-- The genuine kernel pair of the geometric edge projection. -/
abbrev binaryEdgeRelation :=
  {p : binaryEdgeSpace × binaryEdgeSpace // binaryEdgeProjection p.1 = binaryEdgeProjection p.2}

instance binaryEdgeRelation_compact : CompactSpace binaryEdgeRelation :=
  isCompact_iff_compactSpace.mp
    (isClosed_eq (binaryEdgeProjection.continuous.comp continuous_fst)
      (binaryEdgeProjection.continuous.comp continuous_snd)).isCompact

/-- The closed fiber at infinity carries the retained limiting locations. -/
abbrev binaryEdgeInfinity := {p : binaryEdgeSpace // binaryEdgeProjection p = ∞}

instance binaryEdgeInfinity_compact : CompactSpace binaryEdgeInfinity :=
  isCompact_iff_compactSpace.mp
    (isClosed_eq binaryEdgeProjection.continuous continuous_const).isCompact

def binaryEdgeRelationDiagonal : C(binaryEdgeSpace, binaryEdgeRelation) :=
  ⟨fun p => ⟨(p, p), rfl⟩, (continuous_id.prodMk continuous_id).subtype_mk _⟩

def binaryEdgeRelationInfinity :
    C(binaryEdgeInfinity × binaryEdgeInfinity, binaryEdgeRelation) :=
  ⟨fun p => ⟨(p.1.val, p.2.val), p.1.property.trans p.2.property.symm⟩,
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)).subtype_mk _⟩

/-- Covering the relation by its diagonal and infinity pieces is a genuine
continuous surjection, including all limiting fibers. -/
def binaryEdgeRelationCover :
    C(binaryEdgeSpace ⊕ (binaryEdgeInfinity × binaryEdgeInfinity), binaryEdgeRelation) :=
  ⟨Sum.elim binaryEdgeRelationDiagonal binaryEdgeRelationInfinity,
    continuous_sum_dom.mpr ⟨binaryEdgeRelationDiagonal.continuous,
      binaryEdgeRelationInfinity.continuous⟩⟩

theorem binaryEdgeRelationCover_surjective : Function.Surjective binaryEdgeRelationCover := by
  intro r
  cases hp : binaryEdgeProjection r.val.1 with
  | infty =>
    refine ⟨Sum.inr (⟨r.val.1, hp⟩, ⟨r.val.2, ?_⟩), ?_⟩
    · exact r.property.symm.trans hp
    · rfl
  | coe n =>
    have h₁ := binaryEdge_finite_fiber r.val.1 n hp
    have h₂ := binaryEdge_finite_fiber r.val.2 n (r.property.symm.trans hp)
    refine ⟨Sum.inl r.val.1, ?_⟩
    apply Subtype.ext
    change (r.val.1, r.val.1) = r.val
    exact Prod.ext rfl (h₁.trans h₂.symm)

/-- This relation cover is epimorphic in the actual light condensed site. -/
theorem binaryEdgeRelationCover_condensed_epi :
    Epi (topCatToLightCondSet.map (TopCat.ofHom binaryEdgeRelationCover)) :=
  by
    letI : MetricSpace binaryEdgeSpace := metrizableSpaceMetric _
    letI : MetricSpace (binaryEdgeInfinity × binaryEdgeInfinity) := metrizableSpaceMetric _
    letI : MetricSpace (binaryEdgeSpace ⊕ (binaryEdgeInfinity × binaryEdgeInfinity)) :=
      Metric.metricSpaceSum
    exact compactCover_condensed_epi
      (K := TopCat.of (binaryEdgeSpace ⊕ (binaryEdgeInfinity × binaryEdgeInfinity)))
      (TopCat.ofHom binaryEdgeRelationCover) binaryEdgeRelationCover_surjective

/-- Infinity-edge differences vanish by equality of continuous maps, before
free extension or sheaf descent. -/
theorem binaryEdgeInfinity_endpoints :
    binaryEdgeStart.comp (⟨Subtype.val, continuous_subtype_val⟩ :
      C(binaryEdgeInfinity, binaryEdgeSpace)) =
      binaryEdgeEnd.comp (⟨Subtype.val, continuous_subtype_val⟩ :
        C(binaryEdgeInfinity, binaryEdgeSpace)) := by
  ext p
  exact congrArg Subtype.val (binaryEdge_infty_fiber p.val p.property)

end CWComparison

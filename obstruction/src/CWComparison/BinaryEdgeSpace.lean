/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in src/licenses/LICENSE.LeanCondensed.
-/
import CWComparison.BinaryEdges
import CWComparison.CompactCover

noncomputable section
open CategoryTheory Limits Filter Topology OnePoint

namespace CWComparison

def binaryEdgePoint (n : ℕ) : binaryEdgeSpace :=
  ⟨(OnePoint.some n, binaryEdgeA n, binaryEdgeB n), subset_closure ⟨n, rfl⟩⟩

def binaryEdgeProjection : C(binaryEdgeSpace, OnePoint ℕ) :=
  ⟨fun p => p.val.1, continuous_fst.comp continuous_subtype_val⟩

def binaryEdgeStart : C(binaryEdgeSpace, unitInterval) :=
  ⟨fun p => p.val.2.1, continuous_fst.comp (continuous_snd.comp continuous_subtype_val)⟩

def binaryEdgeEnd : C(binaryEdgeSpace, unitInterval) :=
  ⟨fun p => p.val.2.2, continuous_snd.comp (continuous_snd.comp continuous_subtype_val)⟩

/-- No extra edge is introduced in a finite fiber of the compact closure. -/
theorem binaryEdge_finite_fiber (p : binaryEdgeSpace) (n : ℕ)
    (hn : binaryEdgeProjection p = OnePoint.some n) :
    p = binaryEdgePoint n := by
  have ho : IsOpen ({OnePoint.some n} : Set (OnePoint ℕ)) := by
    simpa using OnePoint.isOpenEmbedding_coe.isOpenMap _ (isOpen_discrete ({n} : Set ℕ))
  have hc : IsClosed {q : OnePoint ℕ × unitInterval × unitInterval |
      q.1 ≠ OnePoint.some n ∨ q.2 = (binaryEdgeA n, binaryEdgeB n)} := by
    change IsClosed ((Prod.fst ⁻¹' ({OnePoint.some n} : Set (OnePoint ℕ))ᶜ) ∪
      (Prod.snd ⁻¹' {(binaryEdgeA n, binaryEdgeB n)}))
    exact (ho.isClosed_compl.preimage continuous_fst).union
      (isClosed_singleton.preimage continuous_snd)
  have hs : Set.range (fun k => (OnePoint.some k, binaryEdgeA k, binaryEdgeB k)) ⊆
      {q : OnePoint ℕ × unitInterval × unitInterval |
        q.1 ≠ OnePoint.some n ∨ q.2 = (binaryEdgeA n, binaryEdgeB n)} := by
    rintro _ ⟨k, rfl⟩
    by_cases h : k = n
    · subst k; exact Or.inr rfl
    · exact Or.inl (fun w => h (Option.some.inj w))
  have h := closure_minimal hs hc p.property
  have he : p.val.2 = (binaryEdgeA n, binaryEdgeB n) := h.resolve_left (not_not.mpr hn)
  apply Subtype.ext
  exact Prod.ext hn he

/-- The continuous extended length equation controls every accumulation point. -/
theorem binaryEdge_length_equation (p : binaryEdgeSpace) :
    (binaryEdgeEnd p : ℝ) - (binaryEdgeStart p : ℝ) =
      binaryEdgeLength (binaryEdgeProjection p) := by
  have hc : IsClosed {q : OnePoint ℕ × unitInterval × unitInterval |
      (q.2.2 : ℝ) - (q.2.1 : ℝ) = binaryEdgeLength q.1} := by
    apply isClosed_eq
    · fun_prop
    · exact binaryEdgeLength.continuous.comp continuous_fst
  have hs : Set.range (fun n => (OnePoint.some n, binaryEdgeA n, binaryEdgeB n)) ⊆
      {q : OnePoint ℕ × unitInterval × unitInterval |
        (q.2.2 : ℝ) - (q.2.1 : ℝ) = binaryEdgeLength q.1} := by
    rintro _ ⟨n, rfl⟩
    rfl
  exact closure_minimal hs hc p.property

/-- At infinity the two retained locations coincide; their free difference is zero. -/
theorem binaryEdge_infty_fiber (p : binaryEdgeSpace)
    (hp : binaryEdgeProjection p = ∞) : binaryEdgeStart p = binaryEdgeEnd p := by
  apply Subtype.ext
  have h := binaryEdge_length_equation p
  rw [hp] at h
  change (binaryEdgeEnd p : ℝ) - (binaryEdgeStart p : ℝ) = 0 at h
  exact (sub_eq_zero.mp h).symm

/-- Compactness and the density of finite points give a genuinely surjective map. -/
theorem binaryEdgeProjection_surjective : Function.Surjective binaryEdgeProjection := by
  have hc : IsClosed (Set.range binaryEdgeProjection) :=
    isCompact_range binaryEdgeProjection.continuous |>.isClosed
  have hs : Set.range (OnePoint.some : ℕ → OnePoint ℕ) ⊆ Set.range binaryEdgeProjection := by
    rintro _ ⟨n, rfl⟩
    exact ⟨binaryEdgePoint n, rfl⟩
  intro r
  have hr : r ∈ closure (Set.range (OnePoint.some : ℕ → OnePoint ℕ)) :=
    OnePoint.denseRange_coe r
  exact closure_minimal hs hc hr

/-- The actual geometric parameter is an epimorphic cover of the convergent
sequence object in the light condensed site. -/
theorem binaryEdgeProjection_condensed_epi :
    Epi (topCatToLightCondSet.map (TopCat.ofHom binaryEdgeProjection)) :=
  compactCover_condensed_epi (K := TopCat.of binaryEdgeSpace)
    (TopCat.ofHom binaryEdgeProjection) binaryEdgeProjection_surjective

end CWComparison

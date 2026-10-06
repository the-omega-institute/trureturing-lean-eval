/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in src/licenses/LICENSE.LeanCondensed.
-/
import CWComparison.BinaryEdgeSpace
import CWComparison.BinaryShift

noncomputable section
open CategoryTheory Limits Topology OnePoint

namespace CWComparison

def intervalMidpoint : C(unitInterval × unitInterval, unitInterval) where
  toFun p := ⟨((p.1 : ℝ) + (p.2 : ℝ)) / 2, by
    constructor
    · linarith [unitInterval.nonneg p.1, unitInterval.nonneg p.2]
    · linarith [unitInterval.le_one p.1, unitInterval.le_one p.2]⟩
  continuous_toFun := by fun_prop

abbrev binaryEdgeAmbient := OnePoint ℕ × unitInterval × unitInterval

def binaryEdgeLeftAmbient : C(binaryEdgeAmbient, binaryEdgeAmbient) where
  toFun p := (binaryLeft p.1, p.2.1, intervalMidpoint p.2)
  continuous_toFun := by
    exact (binaryLeft.hom.hom.continuous.comp continuous_fst).prodMk
      ((continuous_fst.comp continuous_snd).prodMk
        (intervalMidpoint.continuous.comp continuous_snd))

def binaryEdgeRightAmbient : C(binaryEdgeAmbient, binaryEdgeAmbient) where
  toFun p := (binaryRight p.1, intervalMidpoint p.2, p.2.2)
  continuous_toFun := by
    exact (binaryRight.hom.hom.continuous.comp continuous_fst).prodMk
      ((intervalMidpoint.continuous.comp continuous_snd).prodMk
        (continuous_snd.comp continuous_snd))

private theorem binaryEdgeLeftAmbient_graph :
    Set.MapsTo binaryEdgeLeftAmbient
      (Set.range (fun n => (OnePoint.some n, binaryEdgeA n, binaryEdgeB n)))
      (Set.range (fun n => (OnePoint.some n, binaryEdgeA n, binaryEdgeB n))) := by
  rintro _ ⟨n, rfl⟩
  refine ⟨2 * n + 1, ?_⟩
  apply Prod.ext
  · rfl
  apply Prod.ext <;> apply Subtype.ext
  · simp [binaryEdgeA, binaryEdgeLeftAmbient]
  · simp [binaryEdgeB, binaryEdgeA, binaryEdgeLeftAmbient, intervalMidpoint]

private theorem binaryEdgeRightAmbient_graph :
    Set.MapsTo binaryEdgeRightAmbient
      (Set.range (fun n => (OnePoint.some n, binaryEdgeA n, binaryEdgeB n)))
      (Set.range (fun n => (OnePoint.some n, binaryEdgeA n, binaryEdgeB n))) := by
  rintro _ ⟨n, rfl⟩
  refine ⟨2 * n + 2, ?_⟩
  apply Prod.ext
  · rfl
  apply Prod.ext <;> apply Subtype.ext
  · simp [binaryEdgeA, binaryEdgeB, binaryEdgeRightAmbient, intervalMidpoint]
  · simp [binaryEdgeB, binaryEdgeRightAmbient]

/-- The child operations lift continuously to the whole compact parameter,
including limiting locations, by preservation of the graph closure. -/
def binaryEdgeLeftChild : C(binaryEdgeSpace, binaryEdgeSpace) where
  toFun p := ⟨binaryEdgeLeftAmbient p.val,
    binaryEdgeLeftAmbient_graph.closure binaryEdgeLeftAmbient.continuous p.property⟩
  continuous_toFun := (binaryEdgeLeftAmbient.continuous.comp continuous_subtype_val).subtype_mk _

def binaryEdgeRightChild : C(binaryEdgeSpace, binaryEdgeSpace) where
  toFun p := ⟨binaryEdgeRightAmbient p.val,
    binaryEdgeRightAmbient_graph.closure binaryEdgeRightAmbient.continuous p.property⟩
  continuous_toFun := (binaryEdgeRightAmbient.continuous.comp continuous_subtype_val).subtype_mk _

@[simp] theorem binaryEdgeLeftChild_projection :
    binaryEdgeProjection.comp binaryEdgeLeftChild =
      binaryLeft.hom.hom.comp binaryEdgeProjection := rfl

@[simp] theorem binaryEdgeRightChild_projection :
    binaryEdgeProjection.comp binaryEdgeRightChild =
      binaryRight.hom.hom.comp binaryEdgeProjection := rfl

@[simp] theorem binaryEdgeLeftChild_start :
    binaryEdgeStart.comp binaryEdgeLeftChild = binaryEdgeStart := rfl

@[simp] theorem binaryEdgeRightChild_end :
    binaryEdgeEnd.comp binaryEdgeRightChild = binaryEdgeEnd := rfl

@[simp] theorem binaryEdgeChildren_midpoint :
    binaryEdgeEnd.comp binaryEdgeLeftChild = binaryEdgeStart.comp binaryEdgeRightChild := rfl

end CWComparison

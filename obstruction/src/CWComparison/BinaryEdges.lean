/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in src/licenses/LICENSE.LeanCondensed.

Shrinking binary edges with their genuine compact space of limiting locations.
The indexing and geometry implement the binary-subdivision argument discussed in
Juan Esteban Rodríguez Camargo, Notes on Solid Geometry, arXiv:2603.03012.
-/
import CWComparison.SimplexCover

noncomputable section
open CategoryTheory Limits Filter Topology OnePoint

namespace CWComparison

/-- Breadth-first binary subdivision of the actual interval. -/
def binaryEdge : ℕ → ℝ × ℝ
  | 0 => (0, 1)
  | n + 1 =>
    let p := binaryEdge (n / 2)
    if n % 2 = 0 then (p.1, (p.1 + p.2) / 2)
    else ((p.1 + p.2) / 2, p.2)
termination_by n => n

@[simp] theorem binaryEdge_zero : binaryEdge 0 = (0, 1) := by rw [binaryEdge]

@[simp] theorem binaryEdge_left (n : ℕ) :
    binaryEdge (2 * n + 1) = ((binaryEdge n).1,
      ((binaryEdge n).1 + (binaryEdge n).2) / 2) := by
  rw [binaryEdge]
  simp

@[simp] theorem binaryEdge_right (n : ℕ) :
    binaryEdge (2 * n + 2) = (((binaryEdge n).1 + (binaryEdge n).2) / 2,
      (binaryEdge n).2) := by
  change binaryEdge ((2 * n + 1) + 1) = _
  rw [binaryEdge]
  have hd : (2 * n + 1) / 2 = n := by omega
  simp [hd]

/-- Bounds include a uniform estimate forcing the edge length to zero. -/
theorem binaryEdge_bounds (n : ℕ) :
    0 ≤ (binaryEdge n).1 ∧ (binaryEdge n).1 ≤ (binaryEdge n).2 ∧
      (binaryEdge n).2 ≤ 1 ∧
      ((n : ℝ) + 2) * ((binaryEdge n).2 - (binaryEdge n).1) ≤ 2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => norm_num
    | succ n =>
      have hn : n / 2 < n + 1 := by omega
      obtain ⟨ha, hab, hb, hlen⟩ := ih (n / 2) hn
      have hdiv : n = 2 * (n / 2) + n % 2 := by omega
      rw [binaryEdge]
      split_ifs with he
      · simp only [Prod.fst, Prod.snd]
        have heq : (n : ℝ) = 2 * (n / 2 : ℕ) := by exact_mod_cast (by omega : n = 2 * (n / 2))
        simp only [Nat.cast_add, Nat.cast_one]
        rw [heq]
        constructor
        · exact ha
        constructor
        · linarith
        constructor
        · linarith
        nlinarith
      · have he' : n % 2 = 1 := by omega
        have heq : (n : ℝ) = 2 * (n / 2 : ℕ) + 1 := by
          exact_mod_cast (by omega : n = 2 * (n / 2) + 1)
        simp only [Prod.fst, Prod.snd, Nat.cast_add, Nat.cast_one]
        rw [heq]
        constructor
        · linarith
        constructor
        · linarith
        constructor
        · exact hb
        nlinarith

def binaryEdgeA (n : ℕ) : unitInterval :=
  ⟨(binaryEdge n).1, (binaryEdge_bounds n).1,
    le_trans (binaryEdge_bounds n).2.1 (binaryEdge_bounds n).2.2.1⟩

def binaryEdgeB (n : ℕ) : unitInterval :=
  ⟨(binaryEdge n).2, le_trans (binaryEdge_bounds n).1 (binaryEdge_bounds n).2.1,
    (binaryEdge_bounds n).2.2.1⟩

/-- A bound which is uniform over all positions in a subdivision level. -/
theorem binaryEdge_length_le (n : ℕ) :
    (binaryEdge n).2 - (binaryEdge n).1 ≤ 2 / ((n : ℝ) + 2) := by
  apply (le_div_iff₀ (by positivity : 0 < (n : ℝ) + 2)).2
  simpa only [mul_comm] using (binaryEdge_bounds n).2.2.2

theorem binaryEdge_length_tendsto :
    Tendsto (fun n => (binaryEdge n).2 - (binaryEdge n).1) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
  exact squeeze_zero (fun n => sub_nonneg.mpr (binaryEdge_bounds n).2.1)
    binaryEdge_length_le ht

/-- The length extends continuously to infinity, with value zero. -/
def binaryEdgeLength : C(OnePoint ℕ, ℝ) :=
  OnePoint.continuousMapMkNat (fun n => (binaryEdge n).2 - (binaryEdge n).1)
    0 binaryEdge_length_tendsto

/-- Finite edges together with all their actual accumulation points. -/
def binaryEdgeSet : Set (OnePoint ℕ × unitInterval × unitInterval) :=
  closure (Set.range (fun n => (OnePoint.some n, binaryEdgeA n, binaryEdgeB n)))

/-- Compactness retains the limiting locations, rather than treating finite points
as conservative for condensed sheaves. -/
abbrev binaryEdgeSpace := binaryEdgeSet

instance binaryEdgeSpace_compact : CompactSpace binaryEdgeSpace :=
  isCompact_iff_compactSpace.mp isClosed_closure.isCompact

end CWComparison

/-
Gate L-10 (`klartag_packing`) — the threshold, propagated: `n₁ = 2,073,600`.

`Threshold.lean` (report 25) fixed `n₁ = 839`, which was report 27's *measured* threshold for the
junk hypothesis at `J = 3`.  Report 30 replaced that measurement with a **proof**, and the cheaply
provable threshold is larger: `1440² = 2,073,600`.  `Threshold.lean` is reported and frozen, and
`Final.smallConst` is parameterised by `n₁`, so this successor simply re-instantiates.

**The trade, and why it is free.**  The small branch covers `1 ≤ m < 2,073,600` by the unit ball,
and `Final.smallConst` is a minimum over a finite set either way — a larger finite set, but still
finite, and *never evaluated*: the minimum is symbolic and the theorem is universally quantified.
Nothing downstream sees the difference except the value of the universal constant `c`, which the
challenge statement does not pin.
-/
import Submission.L10.Threshold

namespace Submission.L10.Threshold2

open MeasureTheory Metric Finset Submission.L10 Submission.L10.Threshold
open Submission.L10.ConstructionA Submission.L10.ChainDataInst Submission.L10.Tiling

/-- **The threshold.**  `1440² = 2,073,600` — the cheaply provable `n₁` of
`HJ.junk_endpoint_le_three`, replacing `Threshold.n₁ = 839`. -/
def n₁ : ℕ := 2073600

theorem n₁_eq : n₁ = 1440 ^ 2 := by norm_num [n₁]

theorem n₁_ge_old : Threshold.n₁ ≤ n₁ := by norm_num [n₁, Threshold.n₁]

/-- `Final.smallConst` at the new threshold. -/
noncomputable def smallConst : ℝ := Final.smallConst n₁

theorem smallConst_pos : 0 < smallConst := Final.smallConst_pos n₁

noncomputable def const (c₀ : ℝ) : ℝ := min c₀ smallConst

theorem const_pos {c₀ : ℝ} (hc₀ : 0 < c₀) : 0 < const c₀ :=
  lt_min hc₀ smallConst_pos

/-- **`remaining_of_lemma43` at the new threshold.**  Identical in shape to
`Threshold.remaining_of_lemma43`; only `n₁` moves.  `Threshold.klartag_packing_of_phi` is already
parameterised by `N₁`, so this is a re-instantiation and not a re-proof. -/
theorem remaining_of_lemma43 {c₀ : ℝ} (hc₀ : 0 < c₀)
    (H : ∀ m : ℕ, n₁ ≤ m →
      ∃ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p) (P : Params p (m + 1)),
        ∀ g : Fin (m + 1) → ZMod p, g ≠ 0 →
          (∀ y : Fin (m + 1) → ℤ, y ≠ 0 → ‖toE (m + 1) y‖ ≤ P.R → y ∉ latZ p (m + 1) g) →
          Assembly.ChainOutput P.alpha g c₀) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      let V := EuclideanSpace ℝ (Fin (n + 1))
      ∃ φ : V →ₗ[ℝ] V, let E := φ '' Metric.ball (0 : V) 1
        (MeasureTheory.volume E : EReal) = c * n ^ 2 ∧
        {v ∈ E | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} := by
  refine Threshold.klartag_packing_of_phi (N₁ := n₁) hc₀ ?_
  intro m hm
  obtain ⟨p, hp, hp0, P, hchain⟩ := H m hm
  exact Assembly.exists_phi_of_params P hchain

end Submission.L10.Threshold2

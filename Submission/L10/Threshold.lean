import Submission.L10.Final
import Submission.L10.Assembly

/-!
# Gate L-10 (`klartag_packing`) — the threshold is a number: `n₁ = 839`

Report 27 turned Lemma 4.3's `n₁` from "sufficiently large" into a **number**: the junk hypothesis
`hJ` of `integrand_le`, at the chain's own parameters, needs
`4(log n)^{3/2}/n + 8(log n)³/n ≤ J`, and the smallest `n` that works is **5,069 at `J = 1`** and
**839 at `J = 3`**.  `J = 3` is adopted.

`Final.lean` is reported and frozen and takes `n₁` as a parameter, so nothing there needs changing;
this module instantiates it and supplies the two things the instantiation needs:

1. `klartag_packing_of_phi` — `Final.klartag_packing_of_hyps` with the large-`n` branch stated as
   the `φ` it actually consumes, so `Assembly.exists_phi_of_params` can feed it directly without
   going through `Assembly.Lemma52`.
2. `remaining_of_lemma43` — the challenge statement from exactly the shape brief 28's successor
   will deliver: for every dimension at or above the threshold, a `Params` together with the
   chain's output on it.

## The two indexings, kept straight

The challenge indexes dimension as `m + 1`; the paper's `n` *is* that dimension.  Taking `n₁ = 839`
in the **challenge** index means the chain is used only for `m ≥ 839`, i.e. dimension `m + 1 ≥ 840`,
which is strictly inside report 27's requirement of dimension `≥ 839`.  The small branch then
covers `1 ≤ m < 839`, i.e. dimensions `2` through `839`, by the unit ball.  This is conservative by
one dimension and costs nothing, since `Final.smallConst` is a minimum over a finite set either way.

## Consistency with the chain's own threshold

Report 25 §3.2 measured the chain's good event failing with probability
`(33 n⁷ log n + 4)·e^{−n}`, below `1` from `n = 28` and below `1/(100 log n)` from about `n = 40`.
At `n₁ = 839` that is satisfied with enormous room: Lemma 4.3, not the good event, is what sets the
threshold.
-/

set_option linter.unusedSectionVars false

namespace Submission.L10.Threshold

open MeasureTheory Metric Finset Submission.L10
open Submission.L10.ConstructionA Submission.L10.ChainDataInst Submission.L10.Tiling

/-- **Lemma 4.3's threshold at `J = 3`** (report 27 §0). -/
def n₁ : ℕ := 839

theorem n₁_eq : n₁ = 839 := rfl

/-- The small-dimension constant at the adopted threshold: `min_{1 ≤ m < 839} Vol(B^{m+1})/m²`. -/
noncomputable def smallConst : ℝ := Final.smallConst n₁

theorem smallConst_pos : 0 < smallConst := Final.smallConst_pos n₁

/-- The theorem's constant: `c = min c₀ c₁`, positive. -/
noncomputable def const (c₀ : ℝ) : ℝ := min c₀ smallConst

theorem const_pos {c₀ : ℝ} (hc₀ : 0 < c₀) : 0 < const c₀ :=
  lt_min hc₀ smallConst_pos

/-- **`Final.klartag_packing_of_hyps` with the large-`n` branch in `φ` form.**  `Final.Remaining`
is stated through `Assembly.Lemma52`, which is the *lattice*-level packaging; the `Params` route
(`Assembly.exists_phi_of_params`) produces the `φ` directly, so this variant lets it feed the
endgame without repackaging. -/
theorem klartag_packing_of_phi {N₁ : ℕ} {c₀ : ℝ} (hc₀ : 0 < c₀)
    (H : ∀ m : ℕ, N₁ ≤ m →
      ∃ φ : EuclideanSpace ℝ (Fin (m + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (m + 1)),
        ENNReal.ofReal (c₀ * (m : ℝ) ^ 2) ≤ volume (φ '' Metric.ball 0 1) ∧
        {v ∈ φ '' Metric.ball 0 1 | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0}) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      let V := EuclideanSpace ℝ (Fin (n + 1))
      ∃ φ : V →ₗ[ℝ] V, let E := φ '' Metric.ball (0 : V) 1
        (MeasureTheory.volume E : EReal) = c * n ^ 2 ∧
        {v ∈ E | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} := by
  refine Scaling.klartag_of_volume_ge (min c₀ (Final.smallConst N₁))
    (lt_min hc₀ (Final.smallConst_pos N₁)) ?_
  intro m hm
  by_cases hlarge : N₁ ≤ m
  · obtain ⟨φ, hvol, hint⟩ := H m hlarge
    refine ⟨φ, le_trans (ENNReal.ofReal_le_ofReal ?_) hvol, hint⟩
    exact mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)
  · have hid : (LinearMap.id : EuclideanSpace ℝ (Fin (m + 1)) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin (m + 1))) '' Metric.ball 0 1 = Metric.ball 0 1 := by
      ext v; simp
    refine ⟨LinearMap.id, ?_, ?_⟩
    · rw [hid]
      exact Final.small_volume_ge hm (Nat.lt_of_not_le hlarge) (min_le_right _ _)
    · rw [hid]
      exact Final.integerPoints_ball (m + 1)

/-- **`remaining_of_lemma43`.**  The hypothesis is exactly the shape brief 28's successor
announces: for every dimension at or above the threshold, `Params` exist (Lemma 4.3 closed, with
`839 ≤ n` among its hypotheses) *and* the chain delivers its output on them.  Everything after that
— the transfer, the exactness, the small dimensions, the constant — is proved. -/
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
  refine klartag_packing_of_phi (N₁ := n₁) hc₀ ?_
  intro m hm
  obtain ⟨p, hp, hp0, P, hchain⟩ := H m hm
  exact Assembly.exists_phi_of_params P hchain

end Submission.L10.Threshold

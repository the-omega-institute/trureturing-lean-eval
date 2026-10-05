import Submission.L10.Assembly
import Submission.L10.Scaling

/-!
# Gate L-10 (`klartag_packing`) — final assembly, part 2: the small `n`, the constant, the theorem

Brief 17, goals 3 and 4.  Three pieces remain between `Assembly.lean` and the challenge statement.

* **Small `n`.**  For `1 ≤ n < n₁` no chain is run: the unit ball already works.  `‖v‖ < 1` forces
  `|v i| < 1` for every coordinate, and an *integer* of absolute value `< 1` is `0` — Klartag's
  own remark that the theorem is trivial below any fixed dimension, made precise by the open cube
  `(−1,1)^{n+1}` containing the ball.  The constant is `c₁ = min_{1 ≤ n < n₁} Vol(B^{n+1})/n²`,
  a minimum over a *finite* set, hence positive.
* **`n = 0`.**  Handled inside `Scaling.klartag_of_volume_ge` (report 3): its hypothesis is only
  required for `m ≥ 1`, and `c·0² = 0 = volume {0}` is discharged there.
* **The constant.**  `c := min c₀ c₁`, positive, and both branches of the case split give
  `volume ≥ c·m²` because `c` is below each.

`klartag_packing_of_hyps` is then the challenge statement **verbatim** — its conclusion is copied
character for character from `Challenge.lean`, via `Scaling.klartag_of_volume_ge`, which also
supplies the exactness (`volume = c·n²`, not `≥`) by shrinking.

`Submission.lean` is deliberately **not** touched: wiring the statement is the coordinator's step
after the comparator dry run.
-/

namespace Submission.L10.Final

open MeasureTheory Metric Finset Submission.L10

/-! ## 1. The small dimensions: the unit ball inside the open cube -/

/-- Every coordinate of a Euclidean vector is bounded by its norm. -/
theorem abs_coord_le_norm {N : ℕ} (v : EuclideanSpace ℝ (Fin N)) (i : Fin N) : |v i| ≤ ‖v‖ := by
  rw [EuclideanSpace.norm_eq]
  have hle : ‖v.ofLp i‖ ^ 2 ≤ ∑ j, ‖v.ofLp j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖v.ofLp j‖ ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  have h1 : |v.ofLp i| = Real.sqrt (‖v.ofLp i‖ ^ 2) := by
    rw [Real.sqrt_sq (norm_nonneg _), Real.norm_eq_abs]
  rw [h1]
  exact Real.sqrt_le_sqrt hle

/-- **The unit ball has no non-zero integer point** — the open cube `(−1,1)^N` contains it, and an
integer of absolute value `< 1` is `0`. -/
theorem integerPoints_ball (N : ℕ) :
    {v ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1 |
      ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} := by
  ext v
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, mem_ball, dist_zero_right]
  constructor
  · rintro ⟨hnorm, hint⟩
    ext i
    obtain ⟨k, hk⟩ := hint i
    have hlt : |v i| < 1 := lt_of_le_of_lt (abs_coord_le_norm v i) hnorm
    rw [← hk] at hlt
    have hk0 : k = 0 := by
      by_contra hne
      have h1 : (1 : ℝ) ≤ |(k : ℝ)| := by
        rw [← Int.cast_abs]
        exact_mod_cast Int.one_le_abs (by omega)
      linarith
    have : v i = 0 := by rw [← hk, hk0]; norm_num
    simpa using this
  · rintro rfl
    exact ⟨by simp, fun i => ⟨0, by simp⟩⟩

/-! ## 2. The small constant -/

/-- `Vol(B^N)` as a real number. -/
noncomputable def ballVol (N : ℕ) : ℝ :=
  (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1)).toReal

theorem ballVol_pos (N : ℕ) : 0 < ballVol N := by
  refine ENNReal.toReal_pos (ne_of_gt ?_) (measure_ball_lt_top).ne
  exact measure_ball_pos _ _ zero_lt_one

theorem ofReal_ballVol (N : ℕ) :
    ENNReal.ofReal (ballVol N) = volume (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1) :=
  ENNReal.ofReal_toReal (measure_ball_lt_top).ne

/-- `c₁ = min_{1 ≤ m < n₁} Vol(B^{m+1}) / m²`, a minimum over a finite set. -/
noncomputable def smallConst (n₁ : ℕ) : ℝ :=
  if h : (Finset.Ico 1 n₁).Nonempty then
    (Finset.Ico 1 n₁).inf' h (fun m => ballVol (m + 1) / (m : ℝ) ^ 2)
  else 1

theorem smallConst_pos (n₁ : ℕ) : 0 < smallConst n₁ := by
  rw [smallConst]
  split
  · rename_i h
    rw [Finset.lt_inf'_iff]
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Ico.1 hm).1
    have : (0 : ℝ) < (m : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
      positivity
    exact div_pos (ballVol_pos _) this
  · norm_num

theorem smallConst_le {n₁ m : ℕ} (h1 : 1 ≤ m) (h2 : m < n₁) :
    smallConst n₁ ≤ ballVol (m + 1) / (m : ℝ) ^ 2 := by
  have hmem : m ∈ Finset.Ico 1 n₁ := Finset.mem_Ico.2 ⟨h1, h2⟩
  have hne : (Finset.Ico 1 n₁).Nonempty := ⟨m, hmem⟩
  rw [smallConst, dite_eq_left hne]
  exact Finset.inf'_le _ hmem

/-- The small-dimension bound in the form `klartag_of_volume_ge` consumes. -/
theorem small_volume_ge {n₁ m : ℕ} (h1 : 1 ≤ m) (h2 : m < n₁) {c : ℝ}
    (hc : c ≤ smallConst n₁) :
    ENNReal.ofReal (c * (m : ℝ) ^ 2)
      ≤ volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) := by
  have hm : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h1
  have hmsq : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
  have hle : c * (m : ℝ) ^ 2 ≤ ballVol (m + 1) := by
    have := le_trans hc (smallConst_le h1 h2)
    rw [le_div_iff₀ hmsq] at this
    exact this
  rw [← ofReal_ballVol (m + 1)]
  exact ENNReal.ofReal_le_ofReal hle

/-! ## 3. What remains, and the theorem -/

/-- **The one thing still open**, as a single named hypothesis: for every dimension above `n₁`,
the chain reaches Klartag's Lemma 5.2.  Briefs 15 and 16 discharge it — brief 16 by closing
Lemma 4.3 and so producing `ChainDataInst.Params`, brief 15 by supplying the conditional-step
inputs that let the chain run (report 11 §8's H2, H3, H5′, H6′).  Everything else in the proof is
now a theorem. -/
structure Remaining (n₁ : ℕ) (c₀ : ℝ) : Prop where
  large : ∀ m : ℕ, n₁ ≤ m → Assembly.Lemma52 m c₀

/-- **`klartag_packing`, from the remaining hypothesis.**  The conclusion is the challenge
statement character for character. -/
theorem klartag_packing_of_hyps {n₁ : ℕ} {c₀ : ℝ} (hc₀ : 0 < c₀) (hR : Remaining n₁ c₀) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      let V := EuclideanSpace ℝ (Fin (n + 1))
      ∃ φ : V →ₗ[ℝ] V, let E := φ '' Metric.ball (0 : V) 1
        (MeasureTheory.volume E : EReal) = c * n ^ 2 ∧
        {v ∈ E | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} := by
  refine Scaling.klartag_of_volume_ge (min c₀ (smallConst n₁))
    (lt_min hc₀ (smallConst_pos n₁)) ?_
  intro m hm
  by_cases hlarge : n₁ ≤ m
  · obtain ⟨φ, hvol, hint⟩ := Assembly.exists_phi_of_lemma52 (hR.large m hlarge)
    refine ⟨φ, le_trans (ENNReal.ofReal_le_ofReal ?_) hvol, hint⟩
    exact mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)
  · have hid : (LinearMap.id : EuclideanSpace ℝ (Fin (m + 1)) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin (m + 1))) '' Metric.ball 0 1 = Metric.ball 0 1 := by
      ext v; simp
    refine ⟨LinearMap.id, ?_, ?_⟩
    · rw [hid]
      exact small_volume_ge hm (Nat.lt_of_not_le hlarge) (min_le_right _ _)
    · rw [hid]
      exact integerPoints_ball (m + 1)

end Submission.L10.Final

import Submission.L10.Discharge
import Submission.L10.StepGlue

/-!
# Gate L-10 (`klartag_packing`), brief 34 — the adopted parameters at `h = n⁻⁹`

Report 29 §5 showed that the adopted step size `h = n⁻⁷` (`ChainWiring.stepSizeAdopted`,
`numStepsAdopted = ⌈16 n⁵ log n⌉`) does **not** fit the state invariant's lift budget: `d·η ≈ 1/2`
there, against a budget `a₀ − r₀ < 1`, so the invariant would first hold at `n = 23,150`.  At
`h = n⁻⁹` the same quantity is `≤ √2/n` and the threshold falls to `n = 4,891`.

`ChainWiring.lean` and `Discharge.lean` are reported and frozen (rule 5), so the successors of
their adopted-parameter lemmas live here, at `e = 7` instead of `e = 5`.  Everything is a
re-instantiation of `ChainDrift.numSteps`/`stepSize`, which are parameterised in `e`; nothing is
re-proved.
-/

set_option linter.unusedSectionVars false

namespace Submission.L10.ParamsAdopted2

open MeasureTheory Matrix Finset Module
open Submission.L10 Submission.L10.Increments

noncomputable section

/-- `N = ⌈16 n⁷ log n⌉` — the adopted number of steps at `h = n⁻⁹`. -/
noncomputable def numStepsAdopted2 (n : ℕ) : ℕ := ChainDrift.numSteps n 7

/-- `h = T / N ≤ n⁻⁹` — the adopted step size. -/
noncomputable def stepSizeAdopted2 (n : ℕ) : ℝ := ChainDrift.stepSize n 7

/-- The horizon is hit exactly: `N · h = T`. -/
theorem numStepsAdopted2_mul_stepSizeAdopted2 {n : ℕ} (hn : 3 ≤ n) :
    (numStepsAdopted2 n : ℝ) * stepSizeAdopted2 n = ChainDrift.horizon n := by
  rw [numStepsAdopted2, stepSizeAdopted2, ChainDrift.stepSize,
    mul_div_cancel₀ _ (ne_of_gt (ChainDrift.numSteps_pos hn))]

theorem stepSizeAdopted2_le {n : ℕ} (hn : 3 ≤ n) : stepSizeAdopted2 n ≤ 1 / (n : ℝ) ^ 9 := by
  rw [stepSizeAdopted2]
  have h : ChainDrift.stepSize n 7 ≤ 1 / (n : ℝ) ^ (7 + 2) := ChainDrift.stepSize_le hn
  norm_num at h ⊢
  exact h

theorem stepSizeAdopted2_nonneg {n : ℕ} (hn : 3 ≤ n) : 0 ≤ stepSizeAdopted2 n := by
  rw [stepSizeAdopted2, ChainDrift.stepSize, ChainDrift.horizon]
  have : (0 : ℝ) ≤ Real.log n := le_trans (by norm_num) (ChainDrift.log_pos_of_three hn)
  positivity

/-- The discretisation-error budget improves from `n^{−3/2}` to `n^{−5/2}`. -/
theorem projError_adopted2 {n : ℕ} (hn : 3 ≤ n) :
    (n : ℝ) ^ 2 * Real.sqrt ((n : ℝ) * stepSizeAdopted2 n) ≤ 1 / (n : ℝ) :=
  ChainDrift.proj_error_le hn (by norm_num)

/-- The pinned trade-off `n²T/4 = 4 log n` is untouched: only `N` and `h` change, not `T`. -/
theorem tradeoff_adopted2 {n : ℕ} (hn : n ≠ 0) :
    (n : ℝ) ^ 2 * ChainDrift.horizon n / 4 = 4 * Real.log n := ChainDrift.tradeoff hn

/-- **`η ≤ √2 · n⁻³`** — the per-step threshold `√(2 h d n)` at `h ≤ n⁻⁹`, `d ≤ n²`.
(`Discharge.eta_le` gives `√2 · n⁻²` at `h ≤ n⁻⁷`.) -/
theorem eta2_le {n : ℕ} (hn : 3 ≤ n) :
    Real.sqrt (2 * stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ) * (n : ℝ))
      ≤ Real.sqrt 2 / (n : ℝ) ^ 3 := by
  have hn1 : (1 : ℕ) ≤ n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by
    have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hd := Discharge.card_UT_le_sq hn1
  have hd0 : (0 : ℝ) ≤ (Fintype.card (UT n) : ℝ) := Nat.cast_nonneg _
  have hh := stepSizeAdopted2_le hn
  have hbound : 2 * stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ) * (n : ℝ)
      ≤ 2 / (n : ℝ) ^ 6 := by
    have hA : stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ) ≤ (1 / (n : ℝ) ^ 9) * (n : ℝ) ^ 2 :=
      mul_le_mul hh hd hd0 (by positivity)
    have h1 : 2 * stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ) * (n : ℝ)
        ≤ 2 * (1 / (n : ℝ) ^ 9) * (n : ℝ) ^ 2 * (n : ℝ) := by nlinarith [hA, hnR]
    calc 2 * stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ) * (n : ℝ)
        ≤ 2 * (1 / (n : ℝ) ^ 9) * (n : ℝ) ^ 2 * (n : ℝ) := h1
      _ = 2 / (n : ℝ) ^ 6 := by field_simp
  calc Real.sqrt (2 * stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ) * (n : ℝ))
      ≤ Real.sqrt (2 / (n : ℝ) ^ 6) := Real.sqrt_le_sqrt hbound
    _ = Real.sqrt 2 / (n : ℝ) ^ 3 := by
        rw [Real.sqrt_div' 2 (by positivity), show ((n : ℝ) ^ 6) = ((n : ℝ) ^ 3) ^ 2 by ring,
          Real.sqrt_sq (by positivity)]

/-- **The lift budget: `d · η ≤ √2 / n`.**  This is the inequality the state invariant needs and
that `h = n⁻⁷` fails (there it is `≈ 1/2`, report 29 §5). -/
theorem d_mul_eta2_le {n : ℕ} (hn : 3 ≤ n) :
    (Fintype.card (UT n) : ℝ)
        * Real.sqrt (2 * stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ) * (n : ℝ))
      ≤ Real.sqrt 2 / (n : ℝ) := by
  have hn1 : (1 : ℕ) ≤ n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by
    have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hd := Discharge.card_UT_le_sq hn1
  have hd0 : (0 : ℝ) ≤ (Fintype.card (UT n) : ℝ) := Nat.cast_nonneg _
  have he := eta2_le hn
  have he0 : (0 : ℝ) ≤ Real.sqrt (2 * stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ) * (n : ℝ)) :=
    Real.sqrt_nonneg _
  calc (Fintype.card (UT n) : ℝ)
        * Real.sqrt (2 * stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ) * (n : ℝ))
      ≤ (n : ℝ) ^ 2 * (Real.sqrt 2 / (n : ℝ) ^ 3) := mul_le_mul hd he he0 (by positivity)
    _ = Real.sqrt 2 / (n : ℝ) := by field_simp

/-- **The union-bound cost at the new `N`: `≤ 33 n⁹ log n`.**  (`Discharge.stepGood_cost_le` gives
`33 n⁷ log n` at `N = ⌈16 n⁵ log n⌉`.) -/
theorem stepGood_cost2_le {n : ℕ} (hn : 3 ≤ n) :
    ((numStepsAdopted2 n : ℕ) : ℝ) * ((Fintype.card (UT n) : ℝ) * 2)
      ≤ 33 * (n : ℝ) ^ 9 * Real.log n := by
  have hn1 : (1 : ℕ) ≤ n := by omega
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog1 : (1 : ℝ) ≤ Real.log n := ChainDrift.log_pos_of_three hn
  have hN : ((numStepsAdopted2 n : ℕ) : ℝ) ≤ 16 * (n : ℝ) ^ 7 * Real.log n + 1 :=
    le_of_lt (Nat.ceil_lt_add_one (by positivity))
  have hd := Discharge.card_UT_le_sq hn1
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hpow : (0 : ℝ) ≤ (n : ℝ) ^ 7 := by positivity
  have hstep : ((numStepsAdopted2 n : ℕ) : ℝ) * ((Fintype.card (UT n) : ℝ) * 2)
      ≤ (16 * (n : ℝ) ^ 7 * Real.log n + 1) * ((n : ℝ) ^ 2 * 2) := by
    have h1 : (Fintype.card (UT n) : ℝ) * 2 ≤ (n : ℝ) ^ 2 * 2 := by linarith
    have hc0 : (0 : ℝ) ≤ (Fintype.card (UT n) : ℝ) * 2 := by positivity
    have hb0 : (0 : ℝ) ≤ 16 * (n : ℝ) ^ 7 * Real.log n + 1 := by nlinarith [hlog1, hpow]
    exact mul_le_mul hN h1 hc0 hb0
  refine le_trans hstep ?_
  have hn2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  have h7 : (2 : ℝ) ≤ (n : ℝ) ^ 7 := by
    have h3 : (3 : ℝ) ^ 7 ≤ (n : ℝ) ^ 7 := by gcongr
    norm_num at h3
    linarith
  have hslack : 2 * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 9 * Real.log n := by
    have ha : 2 * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 9 := by
      nlinarith [mul_nonneg hn2 (by linarith : (0 : ℝ) ≤ (n : ℝ) ^ 7 - 2)]
    have hc : (n : ℝ) ^ 9 ≤ (n : ℝ) ^ 9 * Real.log n := by
      nlinarith [hlog1, pow_nonneg hn0.le 9]
    linarith
  nlinarith [hslack, hlog1, pow_nonneg hn0.le 9,
    mul_nonneg (pow_nonneg hn0.le 9) (by linarith : (0:ℝ) ≤ Real.log n)]

end

end Submission.L10.ParamsAdopted2

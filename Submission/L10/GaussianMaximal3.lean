/-
Gate L-10 (`klartag_packing`), brief 63.

**The size hypotheses, discharged.**

Report 58 left three numeric side conditions as hypotheses.  All three follow from `3 ≤ n`:
`ChainWiring.card_UT` gives `card (UT n) = n(n+1)/2 ≥ 6`, the ceiling in
`ParamsAdopted2.numStepsAdopted2` gives `N ≥ 3`, and `2·d·N ≥ 36 > e`.

`B_adopted n` names the constant so brief 62 can refer to it, and §3 shows it is the **first**
moment's term: the second is smaller by the factor `√(h·d)·(2·log K + 2) ≤ 28·n^{−2.5} < 1`.
-/
import Submission.L10.GaussianMaximal2

namespace Submission.L10

open MeasureTheory ProbabilityTheory Set Real Submission.L10.Increments
open scoped ENNReal NNReal

/-! ## 1. The three size hypotheses -/

theorem six_le_card_UT {n : ℕ} (hn : 3 ≤ n) : 6 ≤ Fintype.card (UT n) := by
  rw [ChainWiring.card_UT]
  have h : 12 ≤ n * (n + 1) := by nlinarith
  omega

theorem card_UT_pos {n : ℕ} (hn : 3 ≤ n) : 0 < Fintype.card (UT n) :=
  lt_of_lt_of_le (by norm_num) (six_le_card_UT hn)

theorem three_le_numStepsAdopted2 {n : ℕ} (hn : 3 ≤ n) :
    3 ≤ ParamsAdopted2.numStepsAdopted2 n := by
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog : (1 : ℝ) ≤ Real.log n := ChainDrift.log_pos_of_three hn
  have h7 : (1 : ℝ) ≤ (n : ℝ) ^ 7 := one_le_pow₀ (by linarith)
  have hx : (3 : ℝ) ≤ 16 * (n : ℝ) ^ 7 * Real.log n := by nlinarith
  have hceil : (16 * (n : ℝ) ^ 7 * Real.log n)
      ≤ ((ParamsAdopted2.numStepsAdopted2 n : ℕ) : ℝ) := Nat.le_ceil _
  have : (3 : ℝ) ≤ ((ParamsAdopted2.numStepsAdopted2 n : ℕ) : ℝ) := le_trans hx hceil
  exact_mod_cast this

/-- **`exp 1 ≤ 2·d·N`.**  At `n ≥ 3` the right side is at least `36`. -/
theorem exp_one_le_2dN {n : ℕ} (hn : 3 ≤ n) :
    Real.exp 1 ≤ 2 * (Fintype.card (UT n) : ℝ)
      * ((ParamsAdopted2.numStepsAdopted2 n : ℕ) : ℝ) := by
  have hd : (6 : ℝ) ≤ (Fintype.card (UT n) : ℝ) := by exact_mod_cast six_le_card_UT hn
  have hN : (3 : ℝ) ≤ ((ParamsAdopted2.numStepsAdopted2 n : ℕ) : ℝ) := by
    exact_mod_cast three_le_numStepsAdopted2 hn
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  nlinarith

/-! ## 2. The adopted instance -/

/-- The chain's adopted scale, `c = √h` with `h = ParamsAdopted2.stepSizeAdopted2 n`. -/
noncomputable def cAdopted (n : ℕ) : ℝ := Real.sqrt (ParamsAdopted2.stepSizeAdopted2 n)

/-- **The constant**, named so brief 62 can refer to it: `maximalAtAdopted_step`'s `max` at
`c = cAdopted n`. -/
noncomputable def B_adopted (n : ℕ) : ℝ :=
  max (cAdopted n * Real.sqrt (Fintype.card (UT n) : ℝ)
      * (Real.sqrt (2 * Real.log (2 * (Fintype.card (UT n) : ℝ)
          * ((ParamsAdopted2.numStepsAdopted2 n : ℕ) : ℝ))) + 1))
    ((cAdopted n * Real.sqrt (Fintype.card (UT n) : ℝ)) ^ 2
      * (2 * Real.log (2 * (Fintype.card (UT n) : ℝ)
          * ((ParamsAdopted2.numStepsAdopted2 n : ℕ) : ℝ)) + 2))

theorem stepSizeAdopted2_pos {n : ℕ} (hn : 3 ≤ n) : 0 < ParamsAdopted2.stepSizeAdopted2 n := by
  rw [ParamsAdopted2.stepSizeAdopted2, ChainDrift.stepSize]
  exact div_pos (horizon_pos hn) (ChainDrift.numSteps_pos hn)

theorem cAdopted_pos {n : ℕ} (hn : 3 ≤ n) : 0 < cAdopted n :=
  Real.sqrt_pos.2 (stepSizeAdopted2_pos hn)

/-- **`MaximalAtAdopted` with no hypothesis but `3 ≤ n`.** -/
theorem maximalAtAdopted_adopted {n : ℕ} (hn : 3 ≤ n) :
    DriftStopped4.MaximalAtAdopted (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))
      (ChainSetup.step (cAdopted n)) (B_adopted n) :=
  maximalAtAdopted_step (cAdopted_pos hn) (card_UT_pos hn) (exp_one_le_2dN hn)

/-- **`IntegrableAtIndex` with no hypothesis but `3 ≤ n`.** -/
theorem integrableAtIndex_adopted {n : ℕ} (hn : 3 ≤ n) :
    IntegrableAtIndex (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))
      (ChainSetup.step (cAdopted n)) (ParamsAdopted2.numStepsAdopted2 n) := by
  have hdR : (0 : ℝ) < (Fintype.card (UT n) : ℝ) := by exact_mod_cast card_UT_pos hn
  have hc : 0 < cAdopted n := cAdopted_pos hn
  have hvcoe : ((Real.toNNReal (cAdopted n ^ 2) : ℝ≥0) : ℝ) = cAdopted n ^ 2 :=
    Real.coe_toNNReal _ (sq_nonneg _)
  have hσpos : 0 < cAdopted n * Real.sqrt (Fintype.card (UT n) : ℝ) := by positivity
  have hvpos : (0 : ℝ) < ((Real.toNNReal (cAdopted n ^ 2) : ℝ≥0) : ℝ) := by
    rw [hvcoe]; positivity
  have hσ2 : (cAdopted n * Real.sqrt (Fintype.card (UT n) : ℝ)) ^ 2
      = ((Real.toNNReal (cAdopted n ^ 2) : ℝ≥0) : ℝ) * (Fintype.card (UT n) : ℝ) := by
    rw [hvcoe, mul_pow, Real.sq_sqrt hdR.le]
  exact integrableAtIndex_of_laws hσpos hvpos hσ2
    (fun k p => ChainSetup.step_coord_law (cAdopted n) k p)
    (fun k => ChainSetup.measurable_step (cAdopted n) k) _

/-! ## 3. The scaled majorant -/

/-- **`B_adopted n ≤ 5·√(h·d)·√(log n)`** for `n ≥ 2 073 600`.  The `max` is the first term
because `√(h·d)·(2·log K + 2) ≤ 28·n^{−2.5} < 1`. -/
theorem B_adopted_le {n : ℕ} (hn : 2073600 ≤ n) :
    B_adopted n
      ≤ 5 * Real.sqrt (ParamsAdopted2.stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ))
          * Real.sqrt (Real.log n) := by
  have hn3 : 3 ≤ n := by omega
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hL6 : (6 : ℝ) ≤ Real.log n := six_le_log hn
  have hLn : Real.log n ≤ (n : ℝ) := le_trans (Real.log_le_sub_one_of_pos hn0) (by linarith)
  have hh : 0 < ParamsAdopted2.stepSizeAdopted2 n := stepSizeAdopted2_pos hn3
  have hdR : (0 : ℝ) < (Fintype.card (UT n) : ℝ) := by exact_mod_cast card_UT_pos hn3
  have hd : (Fintype.card (UT n) : ℝ) ≤ (n : ℝ) ^ 2 := Discharge.card_UT_le_sq (by omega)
  have hhle : ParamsAdopted2.stepSizeAdopted2 n ≤ 1 / (n : ℝ) ^ 9 :=
    ParamsAdopted2.stepSizeAdopted2_le hn3
  -- `σ = c·√d = √(h·d)`
  have hσeq : cAdopted n * Real.sqrt (Fintype.card (UT n) : ℝ)
      = Real.sqrt (ParamsAdopted2.stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ)) := by
    rw [cAdopted, ← Real.sqrt_mul hh.le]
  set σ : ℝ := Real.sqrt (ParamsAdopted2.stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ)) with hσ
  have hσ0 : 0 < σ := Real.sqrt_pos.2 (by positivity)
  have hσsq : σ ^ 2 = ParamsAdopted2.stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hσle : σ ^ 2 ≤ 1 / (n : ℝ) ^ 7 := by
    rw [hσsq]
    calc ParamsAdopted2.stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ)
        ≤ (1 / (n : ℝ) ^ 9) * (n : ℝ) ^ 2 := by
          exact mul_le_mul hhle hd hdR.le (by positivity)
      _ = 1 / (n : ℝ) ^ 7 := by field_simp
  -- the logarithm bound
  set K : ℝ := 2 * (Fintype.card (UT n) : ℝ)
    * ((ParamsAdopted2.numStepsAdopted2 n : ℕ) : ℝ) with hK
  have hKle : Real.log K ≤ 10 * Real.log n + 3 := log_two_card_numSteps_le hn
  have hK1 : Real.exp 1 ≤ K := exp_one_le_2dN hn3
  have hlogK0 : (1 : ℝ) ≤ Real.log K := by
    rw [show (1 : ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
    exact Real.log_le_log (Real.exp_pos 1) hK1
  -- the second term is below the first
  have hsmall : σ * (2 * Real.log K + 2) ≤ Real.sqrt (2 * Real.log K) + 1 := by
    have h1 : 2 * Real.log K + 2 ≤ 20 * (n : ℝ) + 8 := by linarith
    have hσn : σ ≤ 1 / (n : ℝ) ^ 3 := by
      have h3 : (0 : ℝ) < 1 / (n : ℝ) ^ 3 := by positivity
      have h6 : (1 : ℝ) / (n : ℝ) ^ 7 ≤ (1 / (n : ℝ) ^ 3) ^ 2 := by
        rw [div_pow, one_pow, ← pow_mul]
        refine one_div_le_one_div_of_le (by positivity) ?_
        exact pow_le_pow_right₀ (by linarith) (by norm_num)
      have h2 : σ ^ 2 ≤ (1 / (n : ℝ) ^ 3) ^ 2 := le_trans hσle h6
      have h4 := Real.sqrt_le_sqrt h2
      rwa [Real.sqrt_sq hσ0.le, Real.sqrt_sq h3.le] at h4
    have hprod : σ * (2 * Real.log K + 2) ≤ (1 / (n : ℝ) ^ 3) * (20 * (n : ℝ) + 8) := by
      exact mul_le_mul hσn h1 (by linarith) (by positivity)
    have hfin : (1 / (n : ℝ) ^ 3) * (20 * (n : ℝ) + 8) ≤ 1 := by
      rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
      nlinarith [pow_pos hn0 3, sq_nonneg ((n : ℝ) - 1)]
    have hone : (1 : ℝ) ≤ Real.sqrt (2 * Real.log K) + 1 := by
      have := Real.sqrt_nonneg (2 * Real.log K); linarith
    linarith
  have hmax : B_adopted n = σ * (Real.sqrt (2 * Real.log K) + 1) := by
    rw [B_adopted, hσeq, ← hK]
    refine max_eq_left ?_
    calc σ ^ 2 * (2 * Real.log K + 2) = σ * (σ * (2 * Real.log K + 2)) := by ring
      _ ≤ σ * (Real.sqrt (2 * Real.log K) + 1) := mul_le_mul_of_nonneg_left hsmall hσ0.le
  rw [hmax]
  calc σ * (Real.sqrt (2 * Real.log K) + 1) ≤ σ * (5 * Real.sqrt (Real.log n)) :=
        mul_le_mul_of_nonneg_left (sqrt_log_majorant hn hKle) hσ0.le
    _ = 5 * σ * Real.sqrt (Real.log n) := by ring

end Submission.L10

/-
Gate L-10 (`klartag_packing`), brief 26.

**Lemma 4.3's integrability certificates.**  Report 24 counted eight open `IntegrableOn`
hypotheses across the chain.  They are eight *instances* of **three** shapes, so three general
lemmas close all eight:

* the pieces' integrand `Φ(y)·(1 − y√t)^{−(n+2)/2}` on any `Ioc A B` inside the window
  (`I1_le`'s `hint`, `I2_le`'s and `I3_le`'s `hint1`, and `pieces_sum_le`'s `i1`, `i2`, `i3`);
* `integrand_le`'s right-hand side on any `Ioc A B` with `A ≥ 1` (`I2_le`'s and `I3_le`'s `hint2`);
* `r^{n−1}·profile` on any sub-interval of the window (`hgbound_final`'s `h1`, `h2`).

All three are the same argument — **bounded and measurable on a set of finite measure** — through
report 16's `integrableOn_of_bounded'`.  The only new work is the measurability of `Phi` and of the
`rpow` factor, and the uniform bound `(1 − y√t)^{−c} ≤ (1/2)^{−c}` on the window.
-/
import Submission.L10.ProfileBound5

namespace Submission.L10

open MeasureTheory Set Real
open scoped ENNReal NNReal

/-! ## 1. Measurability and the uniform `rpow` bound -/

theorem measurable_Phi : Measurable Phi := by
  unfold Phi
  exact measurable_const.min (by fun_prop)

theorem measurable_rpow_factor {s c : ℝ} :
    Measurable (fun y : ℝ => (1 - y * s) ^ (-c)) := by
  measurability

/-- **The uniform bound on the window.**  `y·√t ≤ 1/2` gives `(1 − y√t)^{−c} ≤ (1/2)^{−c}`, with no
`n` and no `t` in it. -/
theorem rpow_factor_le {s c y B : ℝ} (hs : 0 ≤ s) (hyB : y ≤ B)
    (hB : B * s ≤ 1 / 2) (hc : 0 ≤ c) :
    (1 - y * s) ^ (-c) ≤ ((1 : ℝ) / 2) ^ (-c) := by
  have hys : y * s ≤ 1 / 2 := le_trans (mul_le_mul_of_nonneg_right hyB hs) hB
  have h : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  have := rpow_neg_le_of_le (s₁ := y * s) (s₂ := 1 / 2) (c := c) hys (by norm_num) hc
  rwa [h] at this

/-! ## 2. Certificate 1 — the pieces' integrand (closes four of the eight) -/

/-- **`I₁`/`I₂`/`I₃`'s `hint1`, and `pieces_sum_le`'s `i1`, `i2`, `i3`.**  Bounded by
`(1/2)·(1/2)^{−(n+2)/2}` on the window, measurable, finite measure. -/
theorem integrableOn_pieces {t A B : ℝ} {n : ℕ} (hA : 0 ≤ A) (hB : B * Real.sqrt t ≤ 1 / 2) :
    IntegrableOn
      (fun y : ℝ => Phi y * (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2))) (Ioc A B) := by
  have hs : (0 : ℝ) ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hc : (0 : ℝ) ≤ ((n : ℝ) + 2) / 2 := by positivity
  refine integrableOn_of_bounded' measurableSet_Ioc (by simp [Real.volume_Ioc])
    ((measurable_Phi.mul measurable_rpow_factor).aestronglyMeasurable)
    (M := 1 / 2 * ((1 : ℝ) / 2) ^ (-(((n : ℝ) + 2) / 2))) ?_
  intro y hy
  have hy0 : (0 : ℝ) < y := lt_of_le_of_lt hA hy.1
  have hrp0 : (0 : ℝ) < (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2)) := by
    refine Real.rpow_pos_of_pos ?_ _
    have hys : y * Real.sqrt t ≤ 1 / 2 :=
      le_trans (mul_le_mul_of_nonneg_right hy.2 hs) hB
    linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Phi_nonneg hy0) hrp0.le)]
  exact mul_le_mul (Phi_le_half y) (rpow_factor_le hs hy.2 hB hc) hrp0.le (by norm_num)

/-! ## 3. Certificate 2 — `integrand_le`'s right-hand side (closes two more) -/

/-- **`I₂`'s and `I₃`'s `hint2`.**  On `Ioc A B` with `A ≥ 1` the factor `1/y` is at most `1`, so the
whole integrand is bounded by its constant times `1`. -/
theorem integrableOn_rhs {t J A B : ℝ} {n : ℕ} (hA : 1 ≤ A) :
    IntegrableOn (fun y : ℝ =>
      Real.exp J / Real.sqrt (2 * π) * Real.exp ((n : ℝ) ^ 2 * t / 8)
        * (Real.exp (-(y - (n : ℝ) * Real.sqrt t / 2) ^ 2 / 2) / y)) (Ioc A B) := by
  refine integrableOn_of_bounded' measurableSet_Ioc (by simp [Real.volume_Ioc])
    ((measurable_const.mul
      ((Real.measurable_exp.comp (by fun_prop)).div measurable_id)).aestronglyMeasurable)
    (M := Real.exp J / Real.sqrt (2 * π) * Real.exp ((n : ℝ) ^ 2 * t / 8)) ?_
  intro y hy
  have hy1 : (1 : ℝ) ≤ y := le_trans hA hy.1.le
  have hy0 : (0 : ℝ) < y := by linarith
  have hconst : (0 : ℝ) ≤ Real.exp J / Real.sqrt (2 * π) * Real.exp ((n : ℝ) ^ 2 * t / 8) := by
    positivity
  have hfrac : Real.exp (-(y - (n : ℝ) * Real.sqrt t / 2) ^ 2 / 2) / y ≤ 1 := by
    rw [div_le_one hy0]
    refine le_trans (Real.exp_le_one_iff.2
      (by nlinarith [sq_nonneg (y - (n : ℝ) * Real.sqrt t / 2)])) hy1
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hconst (div_nonneg (Real.exp_pos _).le hy0.le))]
  calc Real.exp J / Real.sqrt (2 * π) * Real.exp ((n : ℝ) ^ 2 * t / 8)
        * (Real.exp (-(y - (n : ℝ) * Real.sqrt t / 2) ^ 2 / 2) / y)
      ≤ Real.exp J / Real.sqrt (2 * π) * Real.exp ((n : ℝ) ^ 2 * t / 8) * 1 :=
        mul_le_mul_of_nonneg_left hfrac hconst
    _ = Real.exp J / Real.sqrt (2 * π) * Real.exp ((n : ℝ) ^ 2 * t / 8) := by ring

/-! ## 4. Certificate 3 — `r^{n−1}·profile` on a sub-interval (closes the last two) -/

/-- **`hgbound_final`'s `h1` and `h2`.**  `integrableOn_profile_radial` restricted. -/
theorem integrableOn_profile_sub {a₀ α W t A B : ℝ} {n : ℕ} (hW : 0 ≤ W) (hA : 0 ≤ A) :
    IntegrableOn (fun r : ℝ => r ^ (n - 1) * profile a₀ α W n t r) (Ioc A B) :=
  (integrableOn_profile_radial hW t).mono_set (fun _ hr => lt_of_le_of_lt hA hr.1)

/-! ## 5. Certificates 4 and 5 — the change-of-variables integrands

`shell_integral_le`'s two hypotheses.  Shape 5 is shape 1 with `PhiC` and a constant; shape 4 needs
the Jacobian bounded, which needs `a₀ − √t·y` bounded away from zero on the window — the side
condition `hgap` below, which is where the window radius `Y` is constrained. -/

theorem integrableOn_shell_rhs {α t Y : ℝ} {n : ℕ} (hY : Y * Real.sqrt t ≤ 1 / 2) :
    IntegrableOn (fun y : ℝ => Real.exp (1 / 2) / α ^ n
      * (Real.sqrt t / 2 * (1 - Real.sqrt t * y) ^ (-(((n : ℝ) + 2) / 2))) * PhiC y)
      (Ioc (0 : ℝ) Y) := by
  have hs : (0 : ℝ) ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hc : (0 : ℝ) ≤ ((n : ℝ) + 2) / 2 := by positivity
  have hm1 : Measurable (fun y : ℝ => (1 - Real.sqrt t * y) ^ (-(((n : ℝ) + 2) / 2))) := by
    have hcm : (fun y : ℝ => (1 - Real.sqrt t * y) ^ (-(((n : ℝ) + 2) / 2)))
        = fun y : ℝ => (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2)) := by
      funext y; rw [mul_comm]
    rw [hcm]
    exact measurable_rpow_factor
  refine integrableOn_of_bounded' measurableSet_Ioc (by simp [Real.volume_Ioc])
    ((((hm1.const_mul (Real.sqrt t / 2)).const_mul
      (Real.exp (1 / 2) / α ^ n)).mul measurable_PhiC).aestronglyMeasurable)
    (M := |Real.exp (1 / 2) / α ^ n| * (Real.sqrt t / 2
      * ((1 : ℝ) / 2) ^ (-(((n : ℝ) + 2) / 2))) * (1 / 2)) ?_
  intro y hy
  have hy0 : (0 : ℝ) < y := hy.1
  have hcomm : Real.sqrt t * y = y * Real.sqrt t := mul_comm _ _
  have hrp : (1 - Real.sqrt t * y) ^ (-(((n : ℝ) + 2) / 2))
      ≤ ((1 : ℝ) / 2) ^ (-(((n : ℝ) + 2) / 2)) := by
    rw [hcomm]
    exact rpow_factor_le hs hy.2 hY hc
  have hrp0 : (0 : ℝ) < (1 - Real.sqrt t * y) ^ (-(((n : ℝ) + 2) / 2)) := by
    refine Real.rpow_pos_of_pos ?_ _
    have : y * Real.sqrt t ≤ 1 / 2 := le_trans (mul_le_mul_of_nonneg_right hy.2 hs) hY
    rw [hcomm]; linarith
  rw [Real.norm_eq_abs, abs_mul, abs_mul]
  refine mul_le_mul (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)) ?_ (abs_nonneg _)
    (by positivity)
  · rw [abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left hrp (by positivity)
  · rw [abs_of_nonneg (PhiC_nonneg y)]
    exact PhiC_le_half y

/-- The Jacobian is bounded where `a₀ − √t·y` is bounded away from zero. -/
theorem substDeriv_le {a₀ s y ε : ℝ} (hs : 0 ≤ s) (hε : 0 < ε) (hgap : ε ≤ a₀ - s * y) :
    substDeriv a₀ s y ≤ s / (2 * ε * Real.sqrt ε) := by
  have hu : (0 : ℝ) < a₀ - s * y := lt_of_lt_of_le hε hgap
  have hsq : Real.sqrt ε ≤ Real.sqrt (a₀ - s * y) := Real.sqrt_le_sqrt hgap
  have hsq0 : (0 : ℝ) < Real.sqrt ε := Real.sqrt_pos.2 hε
  rw [substDeriv]
  refine div_le_div_of_nonneg_left hs (by positivity) ?_
  have : 2 * ε * Real.sqrt ε ≤ 2 * (a₀ - s * y) * Real.sqrt (a₀ - s * y) := by
    refine mul_le_mul (by linarith) hsq hsq0.le (by linarith)
  linarith

end Submission.L10

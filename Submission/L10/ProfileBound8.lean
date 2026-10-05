/-
Gate L-10 (`klartag_packing`), brief 28.

**Lemma 4.3's final three**: shape 4's integrability certificate, the junk hypothesis `hJ`, and the
chaining of `ProfileBound5`'s theorems into one `hgbound`.

**On `hJ` and `n₁`.**  Report 27 measured the junk at the chain's parameters:
`4(log n)^{3/2}/n + 8(n+2)(log n)³/n²`, which is `≤ 3` from `n = 839` and `≤ 1` from `n = 5069`.
`J = 3` is adopted.  What is proved here is the *reduction*: the junk is monotone in `y`, so the
`∀ y ∈ Ioc A B` hypothesis follows from the single value at the endpoint.  The endpoint inequality
itself is a named hypothesis — proving `(log n)³/n ≤ c` for all `n ≥ 839` needs a monotonicity
argument in `n` that is out of scope here, and the numbers are recorded in report 28 §2 instead.
-/
import Submission.L10.ProfileBound7

namespace Submission.L10

open MeasureTheory Set Real
open scoped ENNReal NNReal

/-! ## 1. `hJ` — the junk is monotone in `y`, so the endpoint suffices -/

/-- **The junk hypothesis, reduced to its endpoint.**  `y ↦ y·s + c·(y·s)²` is monotone on `y ≥ 0`
for `s, c ≥ 0`, so `hJ`'s `∀ y ∈ Ioc A B` follows from the single value at `y = B`. -/
theorem junk_le_of_endpoint {t B J : ℝ} {n : ℕ}
    (hend : B * Real.sqrt t + ((n : ℝ) + 2) / 2 * (B * Real.sqrt t) ^ 2 ≤ J)
    {y : ℝ} (hy0 : 0 ≤ y) (hyB : y ≤ B) :
    y * Real.sqrt t + ((n : ℝ) + 2) / 2 * (y * Real.sqrt t) ^ 2 ≤ J := by
  have hs : (0 : ℝ) ≤ Real.sqrt t := Real.sqrt_nonneg t
  have h1 : y * Real.sqrt t ≤ B * Real.sqrt t := mul_le_mul_of_nonneg_right hyB hs
  have h2 : (0 : ℝ) ≤ y * Real.sqrt t := mul_nonneg hy0 hs
  have hc : (0 : ℝ) ≤ ((n : ℝ) + 2) / 2 := by positivity
  have h3 : ((n : ℝ) + 2) / 2 * (y * Real.sqrt t) ^ 2
      ≤ ((n : ℝ) + 2) / 2 * (B * Real.sqrt t) ^ 2 := by
    refine mul_le_mul_of_nonneg_left ?_ hc
    exact pow_le_pow_left₀ h2 h1 2
  linarith

/-- The same, in the `∀ y ∈ Ioc A B` shape the pieces take. -/
theorem junk_on_Ioc {t A B J : ℝ} {n : ℕ} (hA : 0 ≤ A)
    (hend : B * Real.sqrt t + ((n : ℝ) + 2) / 2 * (B * Real.sqrt t) ^ 2 ≤ J) :
    ∀ y ∈ Ioc A B, y * Real.sqrt t + ((n : ℝ) + 2) / 2 * (y * Real.sqrt t) ^ 2 ≤ J :=
  fun _ hy => junk_le_of_endpoint hend (le_trans hA hy.1.le) hy.2

/-! ## 2. Shape 4's certificate

`window_gap` (report 27) supplies `substDeriv_le`'s `ε = a₀ − 1/2`; `radiusOf_le_end` bounds the
radius by `W`; `profile_le_half` bounds the profile.  `measurability` does not see through
`profile`, `subst` or `radiusOf` (report 26), so the measurability is assembled by hand. -/

theorem measurable_substDeriv {a₀ s : ℝ} : Measurable (substDeriv a₀ s) := by
  unfold substDeriv
  fun_prop

theorem measurable_radiusOf {a₀ α δ t : ℝ} : Measurable (radiusOf a₀ α δ t) := by
  unfold radiusOf subst
  fun_prop

/-- **Shape 4's certificate.**  The change-of-variables integrand is bounded on the window: the
Jacobian by `window_gap` + `substDeriv_le`, the radius by `radiusOf_le_end`, the profile by `1/2`. -/
theorem integrableOn_shell_lhs {a₀ α W t Y : ℝ} {n : ℕ} (hα : 0 < α) (hε : 0 < a₀ - 1 / 2)
    (hwin : Y * Real.sqrt t ≤ 1 / 2)
    (hWY : ∀ y ∈ Ioc (0 : ℝ) Y, radiusOf a₀ α (Real.sqrt n / 2) t y ≤ W) (hW : 0 ≤ W) :
    IntegrableOn (fun y : ℝ => |substDeriv a₀ (Real.sqrt t) y / α|
      * ((radiusOf a₀ α (Real.sqrt n / 2) t y) ^ (n - 1)
        * profile a₀ α W n t (radiusOf a₀ α (Real.sqrt n / 2) t y))) (Ioc (0 : ℝ) Y) := by
  have hs : (0 : ℝ) ≤ Real.sqrt t := Real.sqrt_nonneg t
  refine integrableOn_of_bounded' measurableSet_Ioc (by simp [Real.volume_Ioc])
    (((measurable_substDeriv.div_const α).abs.mul
      ((measurable_radiusOf.pow_const (n - 1)).mul
        ((measurable_profile_radius t).comp measurable_radiusOf))).aestronglyMeasurable)
    (M := (Real.sqrt t / (2 * (a₀ - 1 / 2) * Real.sqrt (a₀ - 1 / 2)) / α)
      * (W ^ (n - 1) * (1 / 2))) ?_
  intro y hy
  have hy0 : (0 : ℝ) ≤ y := hy.1.le
  have hgap : a₀ - 1 / 2 ≤ a₀ - Real.sqrt t * y := window_gap hy.2 hwin
  have hjac : substDeriv a₀ (Real.sqrt t) y
      ≤ Real.sqrt t / (2 * (a₀ - 1 / 2) * Real.sqrt (a₀ - 1 / 2)) := substDeriv_le hs hε hgap
  have hjac0 : (0 : ℝ) ≤ substDeriv a₀ (Real.sqrt t) y := by
    rw [substDeriv]
    have : (0 : ℝ) < a₀ - Real.sqrt t * y := lt_of_lt_of_le hε hgap
    positivity
  have hrad : radiusOf a₀ α (Real.sqrt n / 2) t y ≤ W := hWY y hy
  have hrad0 : (0 : ℝ) ≤ radiusOf a₀ α (Real.sqrt n / 2) t y := by
    have hup : (0 : ℝ) < subst a₀ (Real.sqrt t) y := subst_pos (lt_of_lt_of_le hε hgap)
    unfold radiusOf
    have : (0 : ℝ) < subst a₀ (Real.sqrt t) y / α := div_pos hup hα
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (abs_nonneg _) (mul_nonneg (pow_nonneg hrad0 _) (profile_nonneg t _)))]
  refine mul_le_mul ?_ ?_ (mul_nonneg (pow_nonneg hrad0 _) (profile_nonneg t _)) (by positivity)
  · rw [abs_of_nonneg (by positivity)]
    exact div_le_div_of_nonneg_right hjac hα.le
  · exact mul_le_mul (pow_le_pow_left₀ hrad0 hrad _) (profile_le_half t _)
      (profile_nonneg t _) (pow_nonneg hW _)

/-! ## 3. The chaining -/

/-- **`hgbound` for the concrete profile, chained.**  `shell_integral_le` → `shell_le_pieces` →
`hgbound_final`, with the constant

  `ρⁿ/(2n) + (e^{1/2}/(n·αⁿ))·(K₁ + K₂ + K₃)·e^{n²t/8}`,  `ρ = radiusOf 0`.

Every hypothesis is now supplied by a lemma of `ProfileBound6`/`ProfileBound7`. -/
theorem hgbound_chained {a₀ α W t Y K : ℝ} {n : ℕ} (hn : 0 < n) (hα : 0 < α) (ht : 0 < t)
    (ha₀ : 1 ≤ a₀) (hY : 0 ≤ Y) (hW0 : 0 ≤ W)
    (hdef : (n : ℝ) * (α * Real.sqrt n / 2) ≤ 1 / 4)
    (hWdef : W = radiusOf a₀ α (Real.sqrt n / 2) t Y)
    (hSc : ∀ y ∈ Icc (0 : ℝ) Y, 0 < a₀ - Real.sqrt t * y)
    (hlow : ∀ y ∈ Ioc (0 : ℝ) Y, (1 : ℝ) / (2 * α) ≤ subst a₀ (Real.sqrt t) y / α)
    (hpos : ∀ y ∈ Ioc (0 : ℝ) Y, 0 < 1 - Real.sqrt t * y)
    (hWY : ∀ y ∈ Ioc (0 : ℝ) Y, radiusOf a₀ α (Real.sqrt n / 2) t y ≤ W)
    (hρ : 0 ≤ radiusOf a₀ α (Real.sqrt n / 2) t 0)
    (hρW : radiusOf a₀ α (Real.sqrt n / 2) t 0 ≤ W)
    (hint1 : IntegrableOn (fun y : ℝ => |substDeriv a₀ (Real.sqrt t) y / α|
      * ((radiusOf a₀ α (Real.sqrt n / 2) t y) ^ (n - 1)
        * profile a₀ α W n t (radiusOf a₀ α (Real.sqrt n / 2) t y))) (Ioc (0 : ℝ) Y))
    (hint2 : IntegrableOn (fun y : ℝ => Real.exp (1 / 2) / α ^ n
      * (Real.sqrt t / 2 * (1 - Real.sqrt t * y) ^ (-(((n : ℝ) + 2) / 2))) * PhiC y)
      (Ioc (0 : ℝ) Y))
    (hpieces : ((n : ℝ) * Real.sqrt t / 2) *
        ∫ y in Ioc (0 : ℝ) Y, Phi y * (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2))
      ≤ K * Real.exp ((n : ℝ) ^ 2 * t / 8)) :
    ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (y ^ (n - 1) * profile a₀ α W n t y)
      ≤ ENNReal.ofReal ((radiusOf a₀ α (Real.sqrt n / 2) t 0) ^ n / (2 * n)
        + Real.exp (1 / 2) / ((n : ℝ) * α ^ n) * K * Real.exp ((n : ℝ) ^ 2 * t / 8)) := by
  have hshell := shell_integral_le hα ht hn ha₀ hY hdef hWdef hSc hlow hpos hWY hint1 hint2
  have hfinal := shell_le_pieces hn hα hshell hpieces
  exact hgbound_final hn hρ hρW hW0 (integrableOn_profile_sub hW0 le_rfl)
    (integrableOn_profile_sub hW0 hρ) hfinal

end Submission.L10

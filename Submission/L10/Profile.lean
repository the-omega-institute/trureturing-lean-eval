/-
Gate L-10 (`klartag_packing`), brief 18.

**The concrete radial profile.**  Every module so far kept Lemma 4.3's integrand abstract; this one
writes it down.  `profile a₀ α W n t r` is Klartag's contact weight
`Φ(t^{−1/2}(a₀ − 1/|x|²))` (p. 18, eq. 51) evaluated on the scaled lattice `x = α·y`, at the
**inner** radius of the unit cube at `r` — the worst point, report 9 §5 — and truncated to the
window `[0, W]`.

**Two Lean artifacts the definition has to absorb.**
* `Phi 0 = 0`, not `1/2`, because `1/0 = 0` in Lean.  `PhiC` caps that.
* `r ↦ (a₀ − r⁻²)/√t` is **not** monotone on all of `ℝ` — it is even in `r`, and `(0:ℝ)⁻¹ = 0`
  puts a spurious `a₀/√t` at the origin.  It cannot be extended monotonically to `r ≤ 0` (the limit
  at `0⁺` is `−∞`), so `profile` guards the low-radius branch explicitly instead.

Both matter: `Lemma43B.dom_of_antitone` wants `Antitone g` **globally**, and `Lemma43B.lean` is
reported and frozen, so the profile has to be built to meet it rather than the lemma weakened.
-/
import Submission.L10.Lemma43D

namespace Submission.L10

open MeasureTheory Set Real
open scoped ENNReal NNReal

/-! ## 1. `Φ`, capped at its value at the origin -/

/-- `Φ` with the paper's `Φ(0) = 1/2` restored.  `Phi 0 = min (1/2) 0 = 0` in Lean. -/
noncomputable def PhiC (y : ℝ) : ℝ := if y ≤ 0 then 1 / 2 else Phi y

theorem PhiC_of_pos {y : ℝ} (hy : 0 < y) : PhiC y = Phi y := by
  rw [PhiC, ite_eq_right (not_le.2 hy)]

theorem PhiC_of_nonpos {y : ℝ} (hy : y ≤ 0) : PhiC y = 1 / 2 := by
  rw [PhiC, ite_eq_left hy]

theorem PhiC_nonneg (y : ℝ) : 0 ≤ PhiC y := by
  rcases le_or_gt y 0 with h | h
  · rw [PhiC_of_nonpos h]; norm_num
  · rw [PhiC_of_pos h]; exact Phi_nonneg h

theorem PhiC_le_half (y : ℝ) : PhiC y ≤ 1 / 2 := by
  rcases le_or_gt y 0 with h | h
  · rw [PhiC_of_nonpos h]
  · rw [PhiC_of_pos h]; exact Phi_le_half y

/-- `Φ` is antitone on `(0,∞)`: both `e^{−y²/2}` and `1/y` decrease. -/
theorem Phi_antitoneOn : AntitoneOn Phi (Ioi (0 : ℝ)) := by
  intro y₁ h₁ y₂ h₂ h
  have hy₁ : (0 : ℝ) < y₁ := h₁
  have hy₂ : (0 : ℝ) < y₂ := h₂
  have hsq : (0 : ℝ) < Real.sqrt (2 * π) := Real.sqrt_pos.2 (by positivity)
  refine min_le_min le_rfl ?_
  have hnum : Real.exp (-y₂ ^ 2 / 2) ≤ Real.exp (-y₁ ^ 2 / 2) :=
    Real.exp_le_exp.2 (by nlinarith)
  calc Real.exp (-y₂ ^ 2 / 2) / (Real.sqrt (2 * π) * y₂)
      ≤ Real.exp (-y₁ ^ 2 / 2) / (Real.sqrt (2 * π) * y₂) :=
        div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ Real.exp (-y₁ ^ 2 / 2) / (Real.sqrt (2 * π) * y₁) := by gcongr

theorem PhiC_antitone : Antitone PhiC := by
  intro y₁ y₂ h
  rcases le_or_gt y₁ 0 with h₁ | h₁
  · rw [PhiC_of_nonpos h₁]
    exact PhiC_le_half y₂
  · have h₂ : (0 : ℝ) < y₂ := lt_of_lt_of_le h₁ h
    rw [PhiC_of_pos h₁, PhiC_of_pos h₂]
    exact Phi_antitoneOn h₁ h₂ h

theorem measurable_PhiC : Measurable PhiC := by
  unfold PhiC Phi
  refine Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const ?_
  exact (measurable_const.min (by fun_prop))

/-! ## 2. The substitution variable `y(r)` -/

/-- `y(r) = t^{−1/2}·(a₀ − r^{−2})`, the paper's substitution variable (p. 20). -/
noncomputable def yOf (a₀ t r : ℝ) : ℝ := (a₀ - (r ^ 2)⁻¹) / Real.sqrt t

/-- `y(·)` is monotone **on `(0,∞)`** — and only there; it is even in `r`. -/
theorem yOf_monotoneOn {a₀ t : ℝ} (ht : 0 < t) : MonotoneOn (yOf a₀ t) (Ioi (0 : ℝ)) := by
  intro r₁ h₁ r₂ h₂ h
  have hr₁ : (0 : ℝ) < r₁ := h₁
  have hr₂ : (0 : ℝ) < r₂ := h₂
  have hsq : Real.sqrt t > 0 := Real.sqrt_pos.2 ht
  have hinv : (r₂ ^ 2)⁻¹ ≤ (r₁ ^ 2)⁻¹ := by
    rw [inv_le_inv₀ (by positivity) (by positivity)]
    nlinarith
  unfold yOf
  exact div_le_div_of_nonneg_right (by linarith) hsq.le

theorem measurable_yOf_uncurry {a₀ : ℝ} :
    Measurable (fun q : ℝ × ℝ => yOf a₀ q.1 q.2) := by
  unfold yOf
  fun_prop

/-! ## 3. The profile -/

/-- **Klartag's Lemma 4.3 integrand, concretely.**

`profile a₀ α W n t r`:
* `0` beyond the window `W` — the shell `R_t` is bounded (eq. 55), and this is what makes the
  profile integrable;
* `1/2` when the inward-shifted, scaled radius `α·(r − √n/2)` is non-positive — below the shell the
  weight is `Φ(0) = 1/2`, and this branch is what keeps the profile globally antitone despite
  `y(·)` being even in `r`;
* `Φ(y(α·(r − √n/2)))` otherwise — the weight at the cube's **inner** radius.
-/
noncomputable def profile (a₀ α W : ℝ) (n : ℕ) (t r : ℝ) : ℝ :=
  if W < r then 0
  else if α * (r - Real.sqrt n / 2) ≤ 0 then 1 / 2
  else PhiC (yOf a₀ t (α * (r - Real.sqrt n / 2)))

variable {a₀ α W : ℝ} {n : ℕ}

theorem profile_nonneg (t r : ℝ) : 0 ≤ profile a₀ α W n t r := by
  unfold profile
  split_ifs
  · exact le_rfl
  · norm_num
  · exact PhiC_nonneg _

theorem profile_le_half (t r : ℝ) : profile a₀ α W n t r ≤ 1 / 2 := by
  unfold profile
  split_ifs
  · norm_num
  · exact le_rfl
  · exact PhiC_le_half _

theorem profile_zero_of_gt {t r : ℝ} (h : W < r) : profile a₀ α W n t r = 0 := by
  rw [profile, ite_eq_left h]

/-- **The profile is globally antitone** — the hypothesis `Lemma43B.dom_of_antitone` needs. -/
theorem profile_antitone {t : ℝ} (hα : 0 < α) (ht : 0 < t) : Antitone (profile a₀ α W n t) := by
  intro r₁ r₂ h
  by_cases hW₂ : W < r₂
  · rw [profile_zero_of_gt hW₂]
    exact profile_nonneg t r₁
  · have hW₁ : ¬ (W < r₁) := fun hc => hW₂ (lt_of_lt_of_le hc h)
    unfold profile
    rw [ite_eq_right hW₂, ite_eq_right hW₁]
    have hshift : α * (r₁ - Real.sqrt n / 2) ≤ α * (r₂ - Real.sqrt n / 2) := by
      apply mul_le_mul_of_nonneg_left _ hα.le
      linarith
    by_cases hz₂ : α * (r₂ - Real.sqrt n / 2) ≤ 0
    · have hz₁ : α * (r₁ - Real.sqrt n / 2) ≤ 0 := le_trans hshift hz₂
      rw [ite_eq_left hz₂, ite_eq_left hz₁]
    · rw [ite_eq_right hz₂]
      by_cases hz₁ : α * (r₁ - Real.sqrt n / 2) ≤ 0
      · rw [ite_eq_left hz₁]
        exact PhiC_le_half _
      · rw [ite_eq_right hz₁]
        refine PhiC_antitone ?_
        exact yOf_monotoneOn ht (not_le.1 hz₁) (not_le.1 hz₂) hshift

/-! ## 4. `hgmeas` — joint measurability -/

/-- **`hgmeas`, discharged.**  `(t, r) ↦ profile a₀ α W n t r` is jointly measurable: it is a
two-branch `if` over measurable sets, with `PhiC ∘ y(·)` measurable on the last branch. -/
theorem measurable_profile_uncurry :
    Measurable (Function.uncurry (profile a₀ α W n)) := by
  unfold Function.uncurry profile
  refine Measurable.ite (measurableSet_lt measurable_const measurable_snd) measurable_const ?_
  refine Measurable.ite
    (measurableSet_le (measurable_const.mul (measurable_snd.sub measurable_const))
      measurable_const) measurable_const ?_
  refine measurable_PhiC.comp ?_
  exact measurable_yOf_uncurry.comp
    (measurable_fst.prodMk (measurable_const.mul (measurable_snd.sub measurable_const)))

/-! ## 5. The window reduction and the integrability certificates

Two steps of `hgbound` that do not depend on the three-piece split, and the three integrability
certificates of `radialWeightData'_of_chain`, instantiated at the concrete profile through brief
16's tools. -/

section Reduction

/-- Fixing the radius leaves a measurable function of `t`. -/
theorem measurable_profile_time (r : ℝ) :
    Measurable (fun t : ℝ => profile a₀ α W n t r) :=
  measurable_profile_uncurry.comp (measurable_id.prodMk measurable_const)

/-- Fixing the time leaves a measurable function of `r`. -/
theorem measurable_profile_radius (t : ℝ) :
    Measurable (profile a₀ α W n t) :=
  measurable_profile_uncurry.comp (measurable_const.prodMk measurable_id)

theorem norm_profile_le (t r : ℝ) : ‖profile a₀ α W n t r‖ ≤ 1 / 2 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (profile_nonneg t r)]
  exact profile_le_half t r

/-- **`hgt`, at the concrete profile.**  Bounded by `Φ ≤ 1/2` on a finite-measure interval. -/
theorem integrableOn_profile_time {T : ℝ} (r : ℝ) :
    IntegrableOn (fun t : ℝ => profile a₀ α W n t r) (Ioc (0 : ℝ) T) :=
  integrableOn_t_of_bounded (M := 1 / 2)
    (fun r => (measurable_profile_time r).aestronglyMeasurable)
    (fun t _ r => norm_profile_le t r) r

/-- **The window reduction.**  The profile vanishes past `W`, so Lemma 4.3's `Ioi 0` integral is
the window integral.  This is the step of `hgbound` that is independent of the three-piece split,
and it is what makes the change of variables applicable at all: `subst '' S` is a bounded shell. -/
theorem lintegral_Ioi_eq_window (hW : 0 ≤ W) (t : ℝ) :
    ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (y ^ (n - 1) * profile a₀ α W n t y)
      = ∫⁻ y in Ioc (0 : ℝ) W, ENNReal.ofReal (y ^ (n - 1) * profile a₀ α W n t y) := by
  have hsplit : Ioi (0 : ℝ) = Ioc (0 : ℝ) W ∪ Ioi W := (Ioc_union_Ioi_eq_Ioi hW).symm
  have hdisj : Disjoint (Ioc (0 : ℝ) W) (Ioi W) :=
    Set.disjoint_left.2 (fun y hy1 hy2 => absurd hy2 (not_lt.2 hy1.2))
  have hzero : ∀ y ∈ Ioi W, ENNReal.ofReal (y ^ (n - 1) * profile a₀ α W n t y) = 0 := by
    intro y hy
    rw [profile_zero_of_gt hy, mul_zero, ENNReal.ofReal_zero]
  have htail : ∫⁻ y in Ioi W, ENNReal.ofReal (y ^ (n - 1) * profile a₀ α W n t y) = 0 := by
    rw [setLIntegral_congr_fun measurableSet_Ioi hzero, lintegral_zero]
  rw [hsplit, lintegral_union measurableSet_Ioi hdisj, htail, add_zero]

/-- **The radial integrability certificate.**  `y ↦ y^{n−1}·g t y` is integrable on `(0,∞)`: it is
bounded on the window and zero past it — brief 16's `integrableOn_Ioi_of_support`. -/
theorem integrableOn_profile_radial (hW : 0 ≤ W) (t : ℝ) :
    IntegrableOn (fun y : ℝ => y ^ (n - 1) * profile a₀ α W n t y) (Ioi (0 : ℝ)) := by
  refine integrableOn_Ioi_of_support hW ?_ (fun y hy => by rw [profile_zero_of_gt hy, mul_zero])
  refine integrableOn_of_bounded' measurableSet_Ioc (by simp [Real.volume_Ioc])
    (((measurable_id.pow_const (n - 1)).mul (measurable_profile_radius t)).aestronglyMeasurable)
    (M := W ^ (n - 1) * (1 / 2)) ?_
  intro y hy
  have hy0 : (0 : ℝ) ≤ y := hy.1.le
  have hyW : y ≤ W := hy.2
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hy0 _) (profile_nonneg t y))]
  exact mul_le_mul (pow_le_pow_left₀ hy0 hyW _) (profile_le_half t y)
    (profile_nonneg t y) (pow_nonneg (le_trans hy0 hyW) _)

end Reduction

end Submission.L10

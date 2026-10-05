/-
Gate L-10 (`klartag_packing`), brief 85e.

**Radial integrability at `windowR2`, and the combined weight's radial bound.**

Report 85d is blocked on `∫(f+g) = ∫f + ∫g` over `Ioi 0`, which needs `IntegrableOn` for both
summands — a Bochner *inequality* `∫ … ≤ C` says nothing, since the Bochner integral of a
non-integrable function is `0`.

**The `∫⁻` route the brief describes is not needed.**  The tree already carries both certificates,
proved by support-plus-boundedness rather than by finiteness of `∫⁻`:

* `Submission.L10.integrableOn_profile_radial` (`Profile.lean:218`) — `y ↦ y^{n−1}·profile … t y`
  on `Ioi 0`, at any fixed `t`, from `0 ≤ W`;
* `Submission.L10.integrableOn_profile_radial_t` (`Lemma43Final.lean:36`) — the same for the
  `t`-integral over `Ioc 0 T`, from `0 ≤ W` and `0 ≤ T`.

Both are general in `W`, so `WindowR2.windowR2` needs only `Lemma43R2.windowR2_nonneg`.  Neither
`hgbound_at2` nor `hgbound'_of_chain2` is used below.

**Kill rule 2.**  Nothing here touches a constant: §2 is an identity and §3 adds the two bounds
already proved, `4·C1R·(8 − 8/n²)` and `C1cR·n²`, with no new factor.
-/
import Submission.L10.Lemma43UniformR2

namespace Submission.L10.Lemma43R3

open MeasureTheory Set Real Submission.L10 Submission.L10.Lemma43R Submission.L10.Lemma43R2
open scoped ENNReal NNReal

/-! ## 1. The two integrability certificates at `windowR2` -/

/-- **The terminal summand is integrable.**  `Profile.integrableOn_profile_radial` at
`t = ChainDrift.horizon n` and `W = WindowR2.windowR2 α n`. -/
theorem integrableOn_radial_terminal2 {α : ℝ} {n : ℕ} (hn : 2073600 ≤ n) (hα : 0 < α) :
    IntegrableOn (fun y : ℝ => y ^ (n - 1) *
        profile (a0C n) α (WindowR2.windowR2 α n) n (ChainDrift.horizon n) y)
      (Ioi (0 : ℝ)) :=
  integrableOn_profile_radial (windowR2_nonneg hn hα) (ChainDrift.horizon n)

/-- **The integrated summand is integrable**, in the `4·∫` shape `fR4`/`fR2` uses. -/
theorem integrableOn_radial_fR2 {α : ℝ} {n : ℕ} (hn : 2073600 ≤ n) (hα : 0 < α) :
    IntegrableOn (fun y : ℝ => y ^ (n - 1) *
        (4 * ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
          profile (a0C n) α (WindowR2.windowR2 α n) n t y))
      (Ioi (0 : ℝ)) := by
  have hW0 : (0 : ℝ) ≤ WindowR2.windowR2 α n := windowR2_nonneg hn hα
  have hT0 : (0 : ℝ) ≤ ChainDrift.horizon n := T_nonneg (by omega)
  have h := (integrableOn_profile_radial_t (a₀ := a0C n) (α := α)
    (W := WindowR2.windowR2 α n) (T := ChainDrift.horizon n) (n := n) hW0 hT0).const_mul 4
  have heq : (fun y : ℝ => y ^ (n - 1) *
        (4 * ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
          profile (a0C n) α (WindowR2.windowR2 α n) n t y))
      = fun y : ℝ => 4 * (y ^ (n - 1) *
        ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
          profile (a0C n) α (WindowR2.windowR2 α n) n t y) := by
    funext y; ring
  rw [heq]
  exact h

/-! ## 2. Additivity of the radial integral on the combined weight -/

/-- **The combined weight's radial integral splits.**  No sign condition on `a`, `b` is needed —
`integral_add` on the two certificates of §1 gives it for all reals; report 74 §4's coefficients
are nonnegative, so the caller always has more than this asks. -/
theorem radial_bound_combined {α a b : ℝ} {n : ℕ} (hn : 2073600 ≤ n) (hα : 0 < α) :
    ∫ y in Ioi (0 : ℝ), y ^ (n - 1) *
        (a * (4 * ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
                profile (a0C n) α (WindowR2.windowR2 α n) n t y)
          + b * profile (a0C n) α (WindowR2.windowR2 α n) n (ChainDrift.horizon n) y)
      = a * (∫ y in Ioi (0 : ℝ), y ^ (n - 1) *
              (4 * ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
                profile (a0C n) α (WindowR2.windowR2 α n) n t y))
        + b * (∫ y in Ioi (0 : ℝ), y ^ (n - 1) *
              profile (a0C n) α (WindowR2.windowR2 α n) n (ChainDrift.horizon n) y) := by
  have hF := integrableOn_radial_fR2 (α := α) (n := n) hn hα
  have hG := integrableOn_radial_terminal2 (α := α) (n := n) hn hα
  have hcongr : ∀ y ∈ Ioi (0 : ℝ), y ^ (n - 1) *
      (a * (4 * ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
              profile (a0C n) α (WindowR2.windowR2 α n) n t y)
        + b * profile (a0C n) α (WindowR2.windowR2 α n) n (ChainDrift.horizon n) y)
      = a * (y ^ (n - 1) * (4 * ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
              profile (a0C n) α (WindowR2.windowR2 α n) n t y))
        + b * (y ^ (n - 1) *
            profile (a0C n) α (WindowR2.windowR2 α n) n (ChainDrift.horizon n) y) :=
    fun y _ => by ring
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr,
    integral_add (hF.const_mul a) (hG.const_mul b),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

/-! ## 3. `Params.radial_bound` for the combined weight -/

/-- **The combined radial bound.**  §2 plus `radial_bound4_of_chain2` and
`radial_bound_terminal2`: the constant is `a·4·C1R·(8 − 8/n²) + b·C1cR·n²`, with no new factor and
the `n²` of the exponent still cancelled by the horizon in the first summand. -/
theorem radial_bound_combined_le {α a b : ℝ} {n : ℕ} (hn : 2073600 ≤ n) (hα : 0 < α)
    (hdef : (n : ℝ) * (α * Real.sqrt n / 2) ≤ 1 / 4) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∫ y in Ioi (0 : ℝ), y ^ (n - 1) *
        (a * (4 * ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
                profile (a0C n) α (WindowR2.windowR2 α n) n t y)
          + b * profile (a0C n) α (WindowR2.windowR2 α n) n (ChainDrift.horizon n) y)
      ≤ a * (4 * C1R α n * (8 - 8 / (n : ℝ) ^ 2)) + b * (C1cR (a0C n) α n * (n : ℝ) ^ 2) := by
  rw [radial_bound_combined hn hα]
  have h1 := radial_bound4_of_chain2 (α := α) (n := n) hn hα hdef
  have h2 := radial_bound_terminal2 (α := α) (n := n) hn hα hdef
  have k1 := mul_le_mul_of_nonneg_left h1 ha
  have k2 := mul_le_mul_of_nonneg_left h2 hb
  linarith

end Submission.L10.Lemma43R3

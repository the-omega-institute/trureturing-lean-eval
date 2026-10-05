/-
Gate L-10 (`klartag_packing`), brief 89.

**The contact threshold inside the uniformity window: `c₃'' = n^{11/4}`.**

Report 82a-finaldischarge §1: `c₃' = 20 000·n²` is not uniform — the count failure sits at
`0.659` while the existence slack grows, and `n³/4` fails the other way.  With `x := c₃·η` the
window is `x·log n` bounded **and** `x ≫ √(log n/n)`, i.e. `n^{2.5}√(log n) ≪ c₃ ≪ n³/log n`.

**The form.**  `c3Adopted'' n := (n:ℝ)^2 * (√√n)^3`.  This *is* `n^{11/4}`, written in radicals
rather than `Real.rpow`, because `WindowR` already carries `qrt_pow_four ((√√n)^4 = n)`,
`qrt_ge (37 ≤ √√n)` and `log_le_four_qrt (log n ≤ 4√√n)`, so every step below is polynomial in
`q := √√n` and needs no `rpow` lemma.  In `q` the definition is simply `q^11`, and `n³ = q^12`, so
`x ≤ √2/q` falls out in one line — and the same `q` carries the log bound.

**Two uniformity facts, both proved, not merely tabulated:**
* `c3eta_log_le : x·log n ≤ 8` for all `n ≥ 2 073 600` — `x ≤ 2/q` and `log n ≤ 4q`, so the `q`
  cancels exactly.  This is the upper edge of the window.
* `c3eta_le : x ≤ 2/√√n`, so `x → 0`; and `count_ratio_le` turns `c3Adopted''_ge` into a count
  failure bounded by `2K/50 653` for every terminal weight `θ_T ≤ K·n²`, uniformly in `n`.

**Kill rule 2.**  `c₃` enters the volume nowhere.  It sets the state's deviation budget
`mAt = a₀ − (r₀ + c₃η)` and the count threshold; the `n²` of the ellipsoid is untouched, and
`mAt ≥ 1/2` still holds, so `WindowR2`'s window does not move (`mR2_le_mAt''`).
-/
import Submission.L10.DriftStopped6b
import Submission.L10.GoodPathBounds

namespace Submission.L10.DriftStopped6c

open MeasureTheory Matrix Finset Module Submission.L10 Submission.L10.Increments
open scoped NNReal RealInnerProductSpace

/-! ## 1. `c₃'' = n^{11/4}`, in radicals -/

/-- **The uniform contact threshold**, `n^{11/4} = n²·(√√n)³`. -/
noncomputable def c3Adopted'' (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * Real.sqrt (Real.sqrt (n : ℝ)) ^ 3

theorem c3Adopted''_nonneg (n : ℕ) : 0 ≤ c3Adopted'' n := by
  rw [c3Adopted'']; positivity

theorem c3Adopted''_pos {n : ℕ} (hn : 0 < n) : 0 < c3Adopted'' n := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hq : 0 < Real.sqrt (Real.sqrt (n : ℝ)) := Real.sqrt_pos.2 (Real.sqrt_pos.2 hn0)
  rw [c3Adopted'']
  exact mul_pos (pow_pos hn0 2) (pow_pos hq 3)

/-- `n² = q^8` for `q = √√n`. -/
theorem sq_eq_qrt {n : ℕ} (hn : 0 ≤ (n : ℝ)) :
    (n : ℝ) ^ 2 = Real.sqrt (Real.sqrt (n : ℝ)) ^ 8 := by
  have h4 : Real.sqrt (Real.sqrt (n : ℝ)) ^ 4 = (n : ℝ) := WindowR.qrt_pow_four hn
  have hrw : (Real.sqrt (Real.sqrt (n : ℝ)) ^ 4) ^ 2
      = Real.sqrt (Real.sqrt (n : ℝ)) ^ 8 := by ring
  rw [← hrw, h4]

/-- `n³ = q^12` for `q = √√n`. -/
theorem cube_eq_qrt {n : ℕ} (hn : 0 ≤ (n : ℝ)) :
    (n : ℝ) ^ 3 = Real.sqrt (Real.sqrt (n : ℝ)) ^ 12 := by
  have h4 : Real.sqrt (Real.sqrt (n : ℝ)) ^ 4 = (n : ℝ) := WindowR.qrt_pow_four hn
  have hrw : (Real.sqrt (Real.sqrt (n : ℝ)) ^ 4) ^ 3
      = Real.sqrt (Real.sqrt (n : ℝ)) ^ 12 := by ring
  rw [← hrw, h4]

/-- **`c₃'' ≥ 37³·n² = 50 653·n²`** — the count threshold beats `20 000·n²` at every `n ≥ n₁`,
and the margin grows like `n^{3/4}`. -/
theorem c3Adopted''_ge {n : ℕ} (hn : 2073600 ≤ n) : 50653 * (n : ℝ) ^ 2 ≤ c3Adopted'' n := by
  have hq : (37 : ℝ) ≤ Real.sqrt (Real.sqrt (n : ℝ)) := WindowR.qrt_ge hn
  have hn2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  have hcube : (37 : ℝ) ^ 3 ≤ Real.sqrt (Real.sqrt (n : ℝ)) ^ 3 :=
    pow_le_pow_left₀ (by norm_num) hq 3
  rw [c3Adopted'']
  nlinarith [hcube, hn2]

/-! ## 2. `x = c₃''·η`: the two uniformity facts -/

/-- **`x ≤ 2/√√n`.**  `c₃''·η ≤ q^11·√2/q^12 = √2/q`.  So `x → 0` like `n^{−1/4}`. -/
theorem c3eta_le {n : ℕ} (hn : 2073600 ≤ n) :
    c3Adopted'' n * DriftStopped6.etaAdopted n ≤ 2 / Real.sqrt (Real.sqrt (n : ℝ)) := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hq : (37 : ℝ) ≤ Real.sqrt (Real.sqrt (n : ℝ)) := WindowR.qrt_ge hn
  have hq0 : (0 : ℝ) < Real.sqrt (Real.sqrt (n : ℝ)) := by linarith
  have hqne : Real.sqrt (Real.sqrt (n : ℝ)) ≠ 0 := ne_of_gt hq0
  have hηnn : 0 ≤ DriftStopped6.etaAdopted n := DriftStopped7.etaAdopted_nonneg (n := n)
  have hη : DriftStopped6.etaAdopted n ≤ Real.sqrt 2 / (n : ℝ) ^ 3 :=
    ParamsAdopted2.eta2_le (by omega)
  have hs2 : Real.sqrt 2 ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt (2 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hc0 : 0 ≤ c3Adopted'' n := c3Adopted''_nonneg n
  have hinv : (0 : ℝ) ≤ 1 / Real.sqrt (Real.sqrt (n : ℝ)) := by positivity
  have hval : c3Adopted'' n * (Real.sqrt 2 / (n : ℝ) ^ 3)
      = Real.sqrt 2 / Real.sqrt (Real.sqrt (n : ℝ)) := by
    rw [c3Adopted'', sq_eq_qrt hn0.le, cube_eq_qrt hn0.le]
    field_simp
  calc c3Adopted'' n * DriftStopped6.etaAdopted n
      ≤ c3Adopted'' n * (Real.sqrt 2 / (n : ℝ) ^ 3) := mul_le_mul_of_nonneg_left hη hc0
    _ = Real.sqrt 2 / Real.sqrt (Real.sqrt (n : ℝ)) := hval
    _ = Real.sqrt 2 * (1 / Real.sqrt (Real.sqrt (n : ℝ))) := div_eq_mul_one_div _ _
    _ ≤ 2 * (1 / Real.sqrt (Real.sqrt (n : ℝ))) := mul_le_mul_of_nonneg_right hs2 hinv
    _ = 2 / Real.sqrt (Real.sqrt (n : ℝ)) := (div_eq_mul_one_div _ _).symm

/-- **`x·log n ≤ 8`, uniformly.**  The upper edge of the uniformity window, proved outright:
`x ≤ 2/q` and `log n ≤ 4q` (`WindowR.log_le_four_qrt`), and the `q` cancels. -/
theorem c3eta_log_le {n : ℕ} (hn : 2073600 ≤ n) :
    c3Adopted'' n * DriftStopped6.etaAdopted n * Real.log n ≤ 8 := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by linarith
  have hq : (37 : ℝ) ≤ Real.sqrt (Real.sqrt (n : ℝ)) := WindowR.qrt_ge hn
  have hq0 : (0 : ℝ) < Real.sqrt (Real.sqrt (n : ℝ)) := by linarith
  have hqne : Real.sqrt (Real.sqrt (n : ℝ)) ≠ 0 := ne_of_gt hq0
  have hL0 : (0 : ℝ) ≤ Real.log n := Real.log_nonneg hn1
  have hL : Real.log n ≤ 4 * Real.sqrt (Real.sqrt (n : ℝ)) := WindowR.log_le_four_qrt hn
  have hx := c3eta_le hn
  have hxq : (0 : ℝ) ≤ 2 / Real.sqrt (Real.sqrt (n : ℝ)) := by positivity
  calc c3Adopted'' n * DriftStopped6.etaAdopted n * Real.log n
      ≤ (2 / Real.sqrt (Real.sqrt (n : ℝ))) * Real.log n :=
        mul_le_mul_of_nonneg_right hx hL0
    _ ≤ (2 / Real.sqrt (Real.sqrt (n : ℝ))) * (4 * Real.sqrt (Real.sqrt (n : ℝ))) :=
        mul_le_mul_of_nonneg_left hL hxq
    _ = 8 := by field_simp; norm_num

/-- `x ≤ 1/4`, the hypothesis every `GoodPathBounds` statement takes. -/
theorem c3Adopted''_eta_le {n : ℕ} (hn : 2073600 ≤ n) :
    c3Adopted'' n * DriftStopped6.etaAdopted n ≤ 1 / 4 := by
  have h := c3eta_le hn
  have hq : (37 : ℝ) ≤ Real.sqrt (Real.sqrt (n : ℝ)) := WindowR.qrt_ge hn
  have hq0 : (0 : ℝ) < Real.sqrt (Real.sqrt (n : ℝ)) := by linarith
  have h2 : 2 / Real.sqrt (Real.sqrt (n : ℝ)) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ hq0 (by norm_num)]
    linarith
  linarith

/-! ## 3. The constant chain at `c₃''` -/

theorem half_le_mAt'' {n : ℕ} (hn : 2073600 ≤ n) :
    (1 : ℝ) / 2 ≤ GoodPathBounds.mAt n (c3Adopted'' n) :=
  GoodPathBounds.half_le_mAt hn (c3Adopted''_eta_le hn)

theorem one_le_MAt'' {n : ℕ} (hn : 2073600 ≤ n) :
    (1 : ℝ) ≤ GoodPathBounds.MAt n (c3Adopted'' n) :=
  GoodPathBounds.one_le_MAt hn (c3Adopted''_nonneg n)

theorem cqAt''_nonneg {n : ℕ} (hn : 2073600 ≤ n) :
    0 ≤ GoodPathBounds.cqAt n (c3Adopted'' n) :=
  GoodPathBounds.cqAt_nonneg hn (c3Adopted''_eta_le hn) (c3Adopted''_nonneg n)

theorem C₁_le'' {n : ℕ} (hn : 2073600 ≤ n) :
    DriftStopped4.C₁ n (GoodPathBounds.mAt n (c3Adopted'' n))
        (GoodPathBounds.cqAt n (c3Adopted'' n)) ≤ 3 * Real.sqrt (n : ℝ) :=
  DriftStopped6b.C₁_le_at hn (c3Adopted''_nonneg n) (c3Adopted''_eta_le hn)

/-- **`SlackHyp` at `c₃''`** — the 62b/77 obligation, unchanged in value. -/
theorem slackHyp'' {n : ℕ} (hn : 2073600 ≤ n) :
    DriftStopped4.SlackHyp n (GoodPathBounds.mAt n (c3Adopted'' n))
      (GoodPathBounds.cqAt n (c3Adopted'' n)) (B_adopted n) DriftStopped6.slackAdopted :=
  DriftStopped6b.slackHyp_at hn (c3Adopted''_nonneg n) (c3Adopted''_eta_le hn)

/-- **The window still does not move.**  `WindowR2.mR2 = a0C − 1/2` is below `mAt n c₃''`. -/
theorem mR2_le_mAt'' {n : ℕ} (hn : 2073600 ≤ n) :
    WindowR2.mR2 n ≤ GoodPathBounds.mAt n (c3Adopted'' n) :=
  WindowR2.mAt_ge_mR2 hn (c3Adopted''_nonneg n) (c3Adopted''_eta_le hn)

/-! ## 4. `countGood`'s failure at `c₃''`, and its uniform bound -/

section Count
variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}

/-- **The count event's failure bound at `c₃''`.** -/
theorem countGood_failure'' (hn : 0 < n) {θT : ℝ} (weight : ι → ℝ)
    (htail : ∀ i ∈ W, (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))).real
      {ω | i ∈ (Chain.chain q W A₀ (ChainSetup.step (Submission.L10.cAdopted n))
        (ParamsAdopted2.numStepsAdopted2 n) ω).2} ≤ 2 * weight i + 0)
    (hθ : ∑ i ∈ W, weight i ≤ θT) :
    (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))).real
        (StateInvariant4.countGood q W A₀ (ChainSetup.step (Submission.L10.cAdopted n))
          (ParamsAdopted2.numStepsAdopted2 n) (c3Adopted'' n))ᶜ
      ≤ (2 * θT + 0) / c3Adopted'' n :=
  GoodPathBounds.countGood_failure (c3Adopted''_pos hn) weight htail hθ

end Count

/-- **The count failure is uniform in `n`.**  For any terminal weight `θ_T ≤ K·n²` the Markov
ratio is at most `2K/50 653`, with no `n` in it — at report 82a's `2θ_T = 13 187.3·n²` that is
`0.260 3`, against `0.659 4` at `c₃' = 20 000·n²`, and the true value `13 187.3·n^{−3/4}` falls
to `0` (`0.241 3` at `n₁`). -/
theorem count_ratio_le {n : ℕ} {θT K : ℝ} (hn : 2073600 ≤ n) (hK : 0 ≤ K)
    (hθ : θT ≤ K * (n : ℝ) ^ 2) :
    (2 * θT + 0) / c3Adopted'' n ≤ 2 * K / 50653 := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hc0 : 0 < c3Adopted'' n := c3Adopted''_pos (by omega)
  have hge := c3Adopted''_ge hn
  have hnum : 2 * θT + 0 ≤ 2 * K * (n : ℝ) ^ 2 := by linarith
  have hk2 : (0 : ℝ) ≤ 2 * K := by linarith
  have hstep : 2 * K * (50653 * (n : ℝ) ^ 2) ≤ 2 * K * c3Adopted'' n :=
    mul_le_mul_of_nonneg_left hge hk2
  rw [div_le_div_iff₀ hc0 (by norm_num : (0 : ℝ) < 50653)]
  linarith [hnum, hstep]

end Submission.L10.DriftStopped6c

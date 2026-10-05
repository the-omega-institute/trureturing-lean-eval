/-
Gate L-10 (`klartag_packing`), brief 89 follow-up — the check, and what `FinalDischarge2` lacks.

**The check.**  `FinalDischarge2` (reported, frozen) does define the `n^{11/4}` threshold, but it
carries **three** declarations only: `c3Adopted''` (`:46`), `c3Adopted''_nonneg` (`:48`) and
`c3Adopted''_eta_le` (`:52`).  It has **none** of `half_le_mAt''`, `one_le_MAt''`, `cqAt''_nonneg`,
`C₁_le''`, `slackHyp''`, `countGood_failure''`, and no uniformity fact — the two limits in its
docstring are asserted, not proved.  This module supplies exactly those, **at `FinalDischarge2`'s
own term**, so the frozen composition needs no rewriting.

**The two forms are the same number, and are not the same term.**
`FinalDischarge2.c3Adopted'' n = n³/√√n`, `DriftStopped6c.c3Adopted'' n = n²·(√√n)³`; with
`q := √√n` these are `q^12/q` and `q^8·q^3`, both `q^11`.  They are *not* `rfl`-equal (one is a
quotient, the other a product), so `c3_eq` is the bridge, and every uniformity fact below is
report 89's transported across it.

**Kill rule 2.**  `c₃` enters the volume nowhere; it sets the state's deviation budget and the
count threshold only.  `mAt ≥ 1/2` still holds, so `WindowR2`'s window does not move
(`mR2_le_mAt''`).
-/
import Submission.L10.FinalDischarge2
import Submission.L10.DriftStopped6c

namespace Submission.L10.DriftStopped6d

open MeasureTheory Matrix Finset Module Submission.L10 Submission.L10.Increments
open scoped NNReal RealInnerProductSpace

/-! ## 1. The bridge -/

/-- **`n²·(√√n)³ = n³/√√n`** — report 89's radical form equals `FinalDischarge2`'s.  Both are
`q^11` for `q = √√n`, but neither reduces to the other by `rfl`. -/
theorem c3_eq {n : ℕ} (hn : 0 < n) :
    DriftStopped6c.c3Adopted'' n = FinalDischarge2.c3Adopted'' n := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hq0 : (0 : ℝ) < Real.sqrt (Real.sqrt (n : ℝ)) :=
    Real.sqrt_pos.2 (Real.sqrt_pos.2 hn0)
  have hqne : Real.sqrt (Real.sqrt (n : ℝ)) ≠ 0 := ne_of_gt hq0
  rw [DriftStopped6c.c3Adopted'', FinalDischarge2.c3Adopted'',
    DriftStopped6c.sq_eq_qrt hn0.le, DriftStopped6c.cube_eq_qrt hn0.le, eq_div_iff hqne]
  ring

theorem c3_pos {n : ℕ} (hn : 0 < n) : 0 < FinalDischarge2.c3Adopted'' n := by
  rw [← c3_eq hn]; exact DriftStopped6c.c3Adopted''_pos hn

/-! ## 2. The uniformity facts, at `FinalDischarge2`'s term -/

/-- **`c₃'' ≥ 37³·n² = 50 653·n²`**, so the count threshold beats `20 000·n²` at every `n ≥ n₁`
and the margin grows like `n^{3/4}`. -/
theorem c3_ge {n : ℕ} (hn : 2073600 ≤ n) :
    50653 * (n : ℝ) ^ 2 ≤ FinalDischarge2.c3Adopted'' n := by
  rw [← c3_eq (by omega)]; exact DriftStopped6c.c3Adopted''_ge hn

/-- **`x := c₃''·η ≤ 2/√√n`** — the slack term is decreasing, like `n^{−1/4}`. -/
theorem c3eta_le {n : ℕ} (hn : 2073600 ≤ n) :
    FinalDischarge2.c3Adopted'' n * DriftStopped6.etaAdopted n
      ≤ 2 / Real.sqrt (Real.sqrt (n : ℝ)) := by
  rw [← c3_eq (by omega)]; exact DriftStopped6c.c3eta_le hn

/-- **`x·log n ≤ 8`, uniformly in `n`** — the upper edge of the uniformity window, proved.  This
is `FinalDischarge2`'s docstring claim "`c₃·η·log n → 0`" as a theorem, with a constant. -/
theorem c3eta_log_le {n : ℕ} (hn : 2073600 ≤ n) :
    FinalDischarge2.c3Adopted'' n * DriftStopped6.etaAdopted n * Real.log n ≤ 8 := by
  rw [← c3_eq (by omega)]; exact DriftStopped6c.c3eta_log_le hn

/-- **The count failure is uniform in `n`.**  For any terminal weight `θ_T ≤ K·n²` the Markov
ratio is at most `2K/50 653`, with no `n` in it; at `2θ_T = 13 187.3·n²` that is `0.260 3`. -/
theorem count_ratio_le {n : ℕ} {θT K : ℝ} (hn : 2073600 ≤ n) (hK : 0 ≤ K)
    (hθ : θT ≤ K * (n : ℝ) ^ 2) :
    (2 * θT + 0) / FinalDischarge2.c3Adopted'' n ≤ 2 * K / 50653 := by
  rw [← c3_eq (by omega : 0 < n)]; exact DriftStopped6c.count_ratio_le hn hK hθ

/-! ## 3. The constant chain `FinalDischarge2` lacks -/

theorem half_le_mAt'' {n : ℕ} (hn : 2073600 ≤ n) :
    (1 : ℝ) / 2 ≤ GoodPathBounds.mAt n (FinalDischarge2.c3Adopted'' n) :=
  GoodPathBounds.half_le_mAt hn (FinalDischarge2.c3Adopted''_eta_le hn)

theorem one_le_MAt'' {n : ℕ} (hn : 2073600 ≤ n) :
    (1 : ℝ) ≤ GoodPathBounds.MAt n (FinalDischarge2.c3Adopted'' n) :=
  GoodPathBounds.one_le_MAt hn (FinalDischarge2.c3Adopted''_nonneg n)

theorem cqAt''_nonneg {n : ℕ} (hn : 2073600 ≤ n) :
    0 ≤ GoodPathBounds.cqAt n (FinalDischarge2.c3Adopted'' n) :=
  GoodPathBounds.cqAt_nonneg hn (FinalDischarge2.c3Adopted''_eta_le hn)
    (FinalDischarge2.c3Adopted''_nonneg n)

theorem C₁_le'' {n : ℕ} (hn : 2073600 ≤ n) :
    DriftStopped4.C₁ n (GoodPathBounds.mAt n (FinalDischarge2.c3Adopted'' n))
        (GoodPathBounds.cqAt n (FinalDischarge2.c3Adopted'' n)) ≤ 3 * Real.sqrt (n : ℝ) :=
  DriftStopped6b.C₁_le_at hn (FinalDischarge2.c3Adopted''_nonneg n)
    (FinalDischarge2.c3Adopted''_eta_le hn)

/-- **`SlackHyp` at `FinalDischarge2`'s threshold** — the 62b/77 obligation, unchanged in value. -/
theorem slackHyp'' {n : ℕ} (hn : 2073600 ≤ n) :
    DriftStopped4.SlackHyp n (GoodPathBounds.mAt n (FinalDischarge2.c3Adopted'' n))
      (GoodPathBounds.cqAt n (FinalDischarge2.c3Adopted'' n)) (B_adopted n)
      DriftStopped6.slackAdopted :=
  DriftStopped6b.slackHyp_at hn (FinalDischarge2.c3Adopted''_nonneg n)
    (FinalDischarge2.c3Adopted''_eta_le hn)

/-- **The window still does not move.** -/
theorem mR2_le_mAt'' {n : ℕ} (hn : 2073600 ≤ n) :
    WindowR2.mR2 n ≤ GoodPathBounds.mAt n (FinalDischarge2.c3Adopted'' n) :=
  WindowR2.mAt_ge_mR2 hn (FinalDischarge2.c3Adopted''_nonneg n)
    (FinalDischarge2.c3Adopted''_eta_le hn)

section Count
variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}

/-- **`countGood`'s failure bound at `FinalDischarge2`'s threshold.** -/
theorem countGood_failure'' (hn : 0 < n) {θT : ℝ} (weight : ι → ℝ)
    (htail : ∀ i ∈ W, (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))).real
      {ω | i ∈ (Chain.chain q W A₀ (ChainSetup.step (Submission.L10.cAdopted n))
        (ParamsAdopted2.numStepsAdopted2 n) ω).2} ≤ 2 * weight i + 0)
    (hθ : ∑ i ∈ W, weight i ≤ θT) :
    (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))).real
        (StateInvariant4.countGood q W A₀ (ChainSetup.step (Submission.L10.cAdopted n))
          (ParamsAdopted2.numStepsAdopted2 n) (FinalDischarge2.c3Adopted'' n))ᶜ
      ≤ (2 * θT + 0) / FinalDischarge2.c3Adopted'' n :=
  GoodPathBounds.countGood_failure (c3_pos hn) weight htail hθ

end Count

end Submission.L10.DriftStopped6d

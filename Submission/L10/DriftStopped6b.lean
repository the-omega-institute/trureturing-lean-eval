/-
Gate L-10 (`klartag_packing`), brief 85a part B.

**The repaired contact threshold.**

Report 82a: `StateInvariant4.wiredGood'` carries ONE `c₃`, used both as the count threshold and
as the state's deviation budget, and `StateSupply.GoodPath` pins it at
`DriftStopped6.c3Adopted n = n²`.  At `n²` the count budget fails by a factor `1.319·10⁴` at every
dimension: `countGood_failure` gives `2θ_T/c₃`, and `2θ_T = 13 187.3·n²`.

This module fixes `c3Adopted' n := 20 000·n²`, so the count failure is `13 187.3/20 000 = 0.659 4`,
and re-proves the 62b/77 constant chain at a **free** admissible `c₃` — every statement below is
general in `c₃` under `0 ≤ c₃` and `c₃·η ≤ 1/4`, so a later change of the constant costs one line,
not a module.  `eta_le_of_le` says every `c₃ ≤ 10⁵·n²` is admissible, which is the whole usable
range (`η ≈ n⁻³`, so `c₃η ≤ 1/4` holds out to `≈ 5·10⁵·n²`).

The reach does **not** move with `c₃` any more: `WindowR2.mR2 = a0C − 1/2` is below `mAt n c₃` for
every admissible `c₃` (`mR2_le_mAt'`), so the window is fixed once and for all.
-/
import Submission.L10.WindowR2
import Submission.L10.DriftStopped7

namespace Submission.L10.DriftStopped6b

open MeasureTheory Matrix Finset Module Submission.L10 Submission.L10.Increments
open scoped NNReal RealInnerProductSpace

/-! ## 1. Admissible contact thresholds -/

/-- **Every `c₃ ≤ 10⁵·n²` is admissible.**  `η ≤ √2·n⁻³` (`ParamsAdopted2.eta2_le`), so
`c₃η ≤ 10⁵√2/n ≤ 0.0965` at `n ≥ 2 073 600`. -/
theorem eta_le_of_le {n : ℕ} {c₃ : ℝ} (hn : 2073600 ≤ n) (_hc0 : 0 ≤ c₃)
    (hc : c₃ ≤ 100000 * (n : ℝ) ^ 2) :
    c₃ * DriftStopped6.etaAdopted n ≤ 1 / 4 := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hηnn : 0 ≤ DriftStopped6.etaAdopted n := DriftStopped7.etaAdopted_nonneg (n := n)
  have hη : DriftStopped6.etaAdopted n ≤ Real.sqrt 2 / (n : ℝ) ^ 3 :=
    ParamsAdopted2.eta2_le (by omega)
  have hs2 : Real.sqrt 2 ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt (2 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have h1 : c₃ * DriftStopped6.etaAdopted n
      ≤ 100000 * (n : ℝ) ^ 2 * (Real.sqrt 2 / (n : ℝ) ^ 3) :=
    mul_le_mul hc hη hηnn (by positivity)
  have hrw : 100000 * (n : ℝ) ^ 2 * (Real.sqrt 2 / (n : ℝ) ^ 3)
      = (100000 * (n : ℝ) ^ 2 * Real.sqrt 2) / (n : ℝ) ^ 3 := by ring
  have h2 : (100000 * (n : ℝ) ^ 2 * Real.sqrt 2) / (n : ℝ) ^ 3 ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]
    have hsq : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
    have hstep1 : 100000 * (n : ℝ) ^ 2 * Real.sqrt 2 ≤ 200000 * (n : ℝ) ^ 2 := by
      nlinarith [hs2, hsq]
    have hstep2 : 200000 * (n : ℝ) ^ 2 ≤ 1 / 4 * (n : ℝ) ^ 3 := by
      nlinarith [mul_nonneg hsq (by linarith : (0 : ℝ) ≤ (n : ℝ) - 800000)]
    linarith
  rw [hrw] at h1
  linarith

/-- **The repaired contact threshold**, `20 000·n²`.  Report 82a's smallest workable value is
`13 187·n²` (where the count failure is exactly `1`); this clears it with the failure at
`0.659 4`. -/
noncomputable def c3Adopted' (n : ℕ) : ℝ := 20000 * (n : ℝ) ^ 2

theorem c3Adopted'_nonneg (n : ℕ) : 0 ≤ c3Adopted' n := by rw [c3Adopted']; positivity

theorem c3Adopted'_pos {n : ℕ} (hn : 0 < n) : 0 < c3Adopted' n := by
  have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [c3Adopted']; positivity

theorem c3Adopted'_le {n : ℕ} : c3Adopted' n ≤ 100000 * (n : ℝ) ^ 2 := by
  have h : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  rw [c3Adopted']; linarith

/-- **`c₃'·η ≤ 1/4`** — the hypothesis every statement below and in `GoodPathBounds` takes. -/
theorem c3Adopted'_eta_le {n : ℕ} (hn : 2073600 ≤ n) :
    c3Adopted' n * DriftStopped6.etaAdopted n ≤ 1 / 4 :=
  eta_le_of_le hn (c3Adopted'_nonneg n) c3Adopted'_le

/-! ## 2. The 62b/77 constant chain at a free admissible `c₃` -/

theorem cqAt_le_half {n : ℕ} {c₃ : ℝ} (hn : 2073600 ≤ n) (hc₃0 : 0 ≤ c₃)
    (hc₃ : c₃ * DriftStopped6.etaAdopted n ≤ 1 / 4) :
    GoodPathBounds.cqAt n c₃ ≤ 1 / 2 := by
  have h := GoodPathBounds.two_le_cqAt_den hn hc₃ hc₃0
  rw [GoodPathBounds.cqAt]
  exact one_div_le_one_div_of_le (by norm_num) h

/-- **`C₁ ≤ 3√n`** at any admissible `c₃` — `DriftStopped7.C₁_le` with `mAdopted`/`cAdopted`
replaced by `mAt`/`cqAt`. -/
theorem C₁_le_at {n : ℕ} {c₃ : ℝ} (hn : 2073600 ≤ n) (hc₃0 : 0 ≤ c₃)
    (hc₃ : c₃ * DriftStopped6.etaAdopted n ≤ 1 / 4) :
    DriftStopped4.C₁ n (GoodPathBounds.mAt n c₃) (GoodPathBounds.cqAt n c₃)
      ≤ 3 * Real.sqrt (n : ℝ) := by
  have hm := GoodPathBounds.half_le_mAt hn hc₃
  have hc := cqAt_le_half hn hc₃0 hc₃
  have hs := DriftStopped7.sqrt_ge_1440 hn
  have hdiv : Real.sqrt (n : ℝ) / GoodPathBounds.mAt n c₃ ≤ 2 * Real.sqrt (n : ℝ) := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [Real.sqrt_nonneg ((n : ℝ)), hm, hs]
  rw [DriftStopped4.C₁]
  linarith

/-- **`SlackHyp` at any admissible `c₃`** — `DriftStopped7.slackHyp_adopted` re-proved at `mAt`,
`cqAt`.  `C₁·2B ≤ 3√n·10/n³ = 30/(n²√n) ≤ 1 = slackAdopted`. -/
theorem slackHyp_at {n : ℕ} {c₃ : ℝ} (hn : 2073600 ≤ n) (hc₃0 : 0 ≤ c₃)
    (hc₃ : c₃ * DriftStopped6.etaAdopted n ≤ 1 / 4) :
    DriftStopped4.SlackHyp n (GoodPathBounds.mAt n c₃) (GoodPathBounds.cqAt n c₃)
      (B_adopted n) DriftStopped6.slackAdopted := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hC := C₁_le_at hn hc₃0 hc₃
  have hB := DriftStopped7.B_adopted_le' hn
  have hB0 := DriftStopped7.B_adopted_nonneg hn
  have hC0 : 0 ≤ DriftStopped4.C₁ n (GoodPathBounds.mAt n c₃) (GoodPathBounds.cqAt n c₃) :=
    DriftStopped4.C₁_nonneg (GoodPathBounds.cqAt_nonneg hn hc₃ hc₃0)
      (by have := GoodPathBounds.half_le_mAt hn hc₃; linarith)
  have hstep : DriftStopped4.C₁ n (GoodPathBounds.mAt n c₃) (GoodPathBounds.cqAt n c₃)
        * (2 * B_adopted n)
      ≤ (3 * Real.sqrt (n : ℝ)) * (2 * (5 / (n : ℝ) ^ 3)) :=
    mul_le_mul hC (by linarith) (by linarith) (by positivity)
  have hfin : (3 * Real.sqrt (n : ℝ)) * (2 * (5 / (n : ℝ) ^ 3)) ≤ 1 := by
    have hn2 : (30 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith [hnR, hn0]
    have hcube : 30 * (n : ℝ) ≤ (n : ℝ) ^ 3 := by nlinarith [hn2, hn0]
    have hsq : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
      nlinarith [Real.sq_sqrt hn0.le, Real.sqrt_nonneg ((n : ℝ)),
        DriftStopped7.sqrt_ge_1440 hn]
    have hval : (3 * Real.sqrt (n : ℝ)) * (2 * (5 / (n : ℝ) ^ 3))
        = 30 * Real.sqrt (n : ℝ) / (n : ℝ) ^ 3 := by ring
    rw [hval, div_le_one (by positivity)]
    linarith
  rw [DriftStopped4.SlackHyp, DriftStopped6.slackAdopted]
  linarith

/-! ## 3. The chain at `c3Adopted'` -/

theorem half_le_mAt' {n : ℕ} (hn : 2073600 ≤ n) :
    (1 : ℝ) / 2 ≤ GoodPathBounds.mAt n (c3Adopted' n) :=
  GoodPathBounds.half_le_mAt hn (c3Adopted'_eta_le hn)

theorem one_le_MAt' {n : ℕ} (hn : 2073600 ≤ n) :
    (1 : ℝ) ≤ GoodPathBounds.MAt n (c3Adopted' n) :=
  GoodPathBounds.one_le_MAt hn (c3Adopted'_nonneg n)

theorem cqAt'_nonneg {n : ℕ} (hn : 2073600 ≤ n) : 0 ≤ GoodPathBounds.cqAt n (c3Adopted' n) :=
  GoodPathBounds.cqAt_nonneg hn (c3Adopted'_eta_le hn) (c3Adopted'_nonneg n)

theorem C₁_le' {n : ℕ} (hn : 2073600 ≤ n) :
    DriftStopped4.C₁ n (GoodPathBounds.mAt n (c3Adopted' n))
        (GoodPathBounds.cqAt n (c3Adopted' n)) ≤ 3 * Real.sqrt (n : ℝ) :=
  C₁_le_at hn (c3Adopted'_nonneg n) (c3Adopted'_eta_le hn)

/-- **`SlackHyp` at the repaired threshold** — the 62b/77 obligation, re-proved. -/
theorem slackHyp' {n : ℕ} (hn : 2073600 ≤ n) :
    DriftStopped4.SlackHyp n (GoodPathBounds.mAt n (c3Adopted' n))
      (GoodPathBounds.cqAt n (c3Adopted' n)) (B_adopted n) DriftStopped6.slackAdopted :=
  slackHyp_at hn (c3Adopted'_nonneg n) (c3Adopted'_eta_le hn)

/-- **The window does not move with `c₃'`.**  `WindowR2.windowR2` is built on `mR2 = a0C − 1/2`,
which is below `mAt n c₃'`, so the band closes at the generic window. -/
theorem mR2_le_mAt' {n : ℕ} (hn : 2073600 ≤ n) :
    WindowR2.mR2 n ≤ GoodPathBounds.mAt n (c3Adopted' n) :=
  WindowR2.mAt_ge_mR2 hn (c3Adopted'_nonneg n) (c3Adopted'_eta_le hn)

/-! ## 4. `countGood`'s failure at the repaired threshold -/

section Count
variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}

/-- **The count event's failure bound at `c₃'`.**  `GoodPathBounds.countGood_failure` at
`c₃ = c3Adopted' n`: the failure is `2θ_T/(20 000·n²)`, and report 82a's `2θ_T = 13 187.3·n²`
makes it `0.659 4`, independent of `n`.  At the frozen `c₃ = n²` the same quantity is
`13 187.3`, i.e. vacuous. -/
theorem countGood_failure' (hn : 0 < n) {θT : ℝ} (weight : ι → ℝ)
    (htail : ∀ i ∈ W, (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))).real
      {ω | i ∈ (Chain.chain q W A₀ (ChainSetup.step (Submission.L10.cAdopted n))
        (ParamsAdopted2.numStepsAdopted2 n) ω).2} ≤ 2 * weight i + 0)
    (hθ : ∑ i ∈ W, weight i ≤ θT) :
    (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))).real
        (StateInvariant4.countGood q W A₀ (ChainSetup.step (Submission.L10.cAdopted n))
          (ParamsAdopted2.numStepsAdopted2 n) (c3Adopted' n))ᶜ
      ≤ (2 * θT + 0) / c3Adopted' n :=
  GoodPathBounds.countGood_failure (c3Adopted'_pos hn) weight htail hθ

end Count

end Submission.L10.DriftStopped6b

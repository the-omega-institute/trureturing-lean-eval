/-
Gate L-10 (`klartag_packing`), brief 95 — the closing file.

Its own namespace, `Submission.L10.FinalTheorem`, so the wiring lines are
`import Submission.L10.FinalTheorem` and `exact Submission.L10.FinalTheorem.klartag_packing_final`.
`FinalDischarge.lean` is a different, older module (brief 82a) with six importers and is untouched.

**What is here so far.** `budget_lt_one` is `hbudget`'s arithmetic core, in the shape the
instantiation produces: after the cancellation the numerator is `O(1)` and the denominator is
`C' − O(1)`, so the Markov ratio is about `2·10⁻³` at the crudest bounds and the count
failure leaves a factor of three unused. The generous constants below are deliberate — the true
ratio is `6.5·10⁻⁵`, so nothing here is tight and no bound needs sharpening later.

**The failure ceiling is `0.27`, not `0.26`.**  `DriftStopped6c.count_ratio_le` at
`2·θ_T = 13 187.3·n²` gives `pcnt = 0.260 3`, and `failTotal` adds its two exponential terms on
top — about `1.7·10⁻⁴¹`, but on top. A ceiling of `0.26` would therefore **not** apply, by `0.0003`.
This is the same trap as report 94a's constant, one level down: a bound that looks harmlessly round
is unusable because something else sits just under it.

The cancellation is the same one `TruncSumMean.hLb_of_bounds` uses, now on the other side:
`driftCen` contributes `+4·log n` to the numerator and `−cqAt·c²·S` contributes `−4·log n`
through 95a's `hS_light_win`, leaving `O(1)`.

Nothing reported is edited.
-/
import Submission.L10.AdoptedConstants95
import Submission.L10.CutVarianceLight
import Submission.L10.ChainShortfall
import Submission.L10.TailWiring
import Submission.L10.Theorem2R5
import Submission.L10.ThetaIntegrated99
import Submission.L10.FailTotalBound99

set_option linter.unusedSectionVars false

namespace Submission.L10.FinalTheorem

open MeasureTheory Matrix Finset Module
open scoped ENNReal NNReal RealInnerProductSpace
open Submission.L10 Submission.L10.Increments Submission.L10.StoppedChain
open Submission.L10.RawDataInst2 Submission.L10.RawDataInst2RW2
open Submission.L10.ConstructionA Submission.L10.Tiling
open Submission.L10.DriftStopped Submission.L10.DriftStopped8R5
open Submission.L10.DriftAccumulated Submission.L10.PaddedLawSetupRW2
open Submission.L10.TailSideSetup2 Submission.L10.TailAtStepR5W2
open Submission.L10.Theorem2R4 Submission.L10.FinalDischarge

/-- **`hbudget`'s arithmetic core.**  A numerator of at most `1000` over a denominator of at least
`499000`, plus a failure budget of at most `0.27`, is below `1` — with a factor of three to spare.
The instantiation supplies `num ≤ 1000` from the `4·log n` cancellation and `den ≥ 499000` from
`hLb`'s own estimate at `C' = 500000`. -/
theorem budget_lt_one {num den F : ℝ} (_hnum0 : 0 ≤ num) (hnum : num ≤ 1000)
    (hden : 499000 ≤ den) (hF : F ≤ 27 / 100) : num / den + F < 1 := by
  have hd0 : (0 : ℝ) < den := by linarith
  have hratio : num / den ≤ 1000 / 499000 := by
    refine div_le_div₀ (by norm_num) hnum (by norm_num) hden
  have hsmall : (1000 : ℝ) / 499000 ≤ 1 / 400 := by norm_num
  linarith

/-- The same with the two constants free, for an instantiation that wants different slack. -/
theorem budget_lt_one' {num den F A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (_hnum0 : 0 ≤ num) (hnum : num ≤ A) (hden : B ≤ den) (hF : F ≤ 27 / 100)
    (hAB : A / B < 73 / 100) : num / den + F < 1 := by
  have hd0 : (0 : ℝ) < den := by linarith
  have hratio : num / den ≤ A / B := div_le_div₀ hA.le hnum hB hden
  linarith


/-- The same with the ceiling on the failure budget free as well. -/
theorem budget_lt_one'' {num den F Anum Bden Fb : ℝ} (hA : 0 ≤ Anum) (hB : 0 < Bden)
    (hnum : num ≤ Anum) (hden : Bden ≤ den) (hF : F ≤ Fb)
    (hsum : Anum / Bden + Fb < 1) : num / den + F < 1 := by
  have hd0 : (0 : ℝ) < den := by linarith
  have hratio : num / den ≤ Anum / Bden := div_le_div₀ hA hnum hB hden
  linarith

/-! ## 1. The quarter root `q = √√n`, and the three small quantities in `1/q` -/

section Qrt

variable {n : ℕ}

/-- `0 < q`. -/
theorem qrt_pos (hn : 2073600 ≤ n) : (0 : ℝ) < Real.sqrt (Real.sqrt (n : ℝ)) := by
  have := WindowR.qrt_ge hn; linarith

/-- **`r₀ ≤ 8/q`.**  `log n/n ≤ 4/q³ ≤ 1/(9q²)` because `q ≥ 36`, and the square root of the
right-hand side is `1/(3q)`. -/
theorem r0_le_qrt (hn : 2073600 ≤ n) :
    DriftStopped6.r0Adopted n ≤ 8 / Real.sqrt (Real.sqrt (n : ℝ)) := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  set qq := Real.sqrt (Real.sqrt (n : ℝ)) with hqdef
  have hq37 : (37 : ℝ) ≤ qq := WindowR.qrt_ge hn
  have hq0 : (0 : ℝ) < qq := by linarith
  have hqne : qq ≠ 0 := ne_of_gt hq0
  have hq4 : qq ^ 4 = (n : ℝ) := WindowR.qrt_pow_four hn0.le
  have hlog : Real.log n ≤ 4 * qq := WindowR.log_le_four_qrt hn
  have hkey : Real.log n / (n : ℝ) ≤ (1 / (3 * qq)) ^ 2 := by
    rw [div_le_iff₀ hn0]
    have hid : (1 / (3 * qq)) ^ 2 * (n : ℝ) = qq ^ 2 / 9 := by
      rw [← hq4]; field_simp; ring
    rw [hid]
    nlinarith [hlog, hq37, hq0]
  have hs : Real.sqrt (Real.log n / (n : ℝ)) ≤ 1 / (3 * qq) := by
    have h0 : (0 : ℝ) ≤ 1 / (3 * qq) := by positivity
    calc Real.sqrt (Real.log n / (n : ℝ))
        ≤ Real.sqrt ((1 / (3 * qq)) ^ 2) := Real.sqrt_le_sqrt hkey
      _ = 1 / (3 * qq) := Real.sqrt_sq h0
  have hid2 : (24 : ℝ) * (1 / (3 * qq)) = 8 / qq := by field_simp; ring
  rw [DriftStopped6.r0Adopted, ← hid2]
  linarith

/-- **`η ≤ 1/q`.**  `η ≤ √2/n³ ≤ 2/q¹² ≤ 1/q`. -/
theorem eta_le_qrt (hn : 2073600 ≤ n) :
    DriftStopped6.etaAdopted n ≤ 1 / Real.sqrt (Real.sqrt (n : ℝ)) := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hq37 : (37 : ℝ) ≤ Real.sqrt (Real.sqrt (n : ℝ)) := WindowR.qrt_ge hn
  have hq0 : (0 : ℝ) < Real.sqrt (Real.sqrt (n : ℝ)) := by linarith
  have hcube : (n : ℝ) ^ 3 = Real.sqrt (Real.sqrt (n : ℝ)) ^ 12 :=
    DriftStopped6c.cube_eq_qrt hn0.le
  have h1 : DriftStopped6.etaAdopted n ≤ Real.sqrt 2 / (n : ℝ) ^ 3 := by
    rw [DriftStopped6.etaAdopted]; exact ParamsAdopted2.eta2_le (by omega)
  have h2 : Real.sqrt 2 ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt (2 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hc0 : (0 : ℝ) < (n : ℝ) ^ 3 := by positivity
  have h4 : Real.sqrt 2 / (n : ℝ) ^ 3 ≤ 2 / (n : ℝ) ^ 3 := by
    rw [div_le_div_iff₀ hc0 hc0]; nlinarith [h2, hc0]
  have hq12 : Real.sqrt (Real.sqrt (n : ℝ)) ^ 2 ≤ Real.sqrt (Real.sqrt (n : ℝ)) ^ 12 :=
    pow_le_pow_right₀ (by linarith) (by norm_num)
  have h3 : (2 : ℝ) / (n : ℝ) ^ 3 ≤ 1 / Real.sqrt (Real.sqrt (n : ℝ)) := by
    rw [div_le_div_iff₀ hc0 hq0, one_mul, hcube]
    nlinarith [hq37, hq0, hq12]
  linarith

/-- `card (UT n) > 0`. -/
theorem card_UT_pos (hn : 3 ≤ n) : (0 : ℝ) < (Fintype.card (UT n) : ℝ) := by
  have hpos : 0 < Fintype.card (UT n) := by
    rw [ChainWiring.card_UT]
    have h34 : 3 * 4 ≤ n * (n + 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  exact_mod_cast hpos

/-- `η > 0`: `η² = 2·h·card·n` and all three factors are positive. -/
theorem eta_pos (hn : 3 ≤ n) : (0 : ℝ) < DriftStopped6.etaAdopted n := by
  have hsq := TruncSumMean.etaAdopted_sq (n := n) hn
  have hh0 : (0 : ℝ) < ParamsAdopted2.stepSizeAdopted2 n :=
    TailSideSetup2.stepSizeAdopted2_pos hn
  have hD := card_UT_pos (n := n) hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have h2 : (0 : ℝ) < DriftStopped6.etaAdopted n ^ 2 := by rw [hsq]; positivity
  exact lt_of_le_of_ne DriftStopped7.etaAdopted_nonneg
    (by intro h; rw [← h] at h2; norm_num at h2)

/-- **`failTotal` is nonnegative.** -/
theorem failTotal_nonneg (hn : 3 ≤ n) {pcnt : ℝ} (hpc : 0 ≤ pcnt) :
    0 ≤ GoodPathBounds.failTotal n pcnt := by
  have hlog0 : (0 : ℝ) ≤ Real.log (n : ℝ) :=
    le_trans (by norm_num) (ChainDrift.log_pos_of_three hn)
  rw [GoodPathBounds.failTotal]
  have ha : (0 : ℝ) ≤ 33 * (n : ℝ) ^ 9 * Real.log (n : ℝ) := mul_nonneg (by positivity) hlog0
  have hb : (0 : ℝ) ≤ (33 * (n : ℝ) ^ 9 * Real.log (n : ℝ) + 4) * Real.exp (-(n : ℝ)) :=
    mul_nonneg (by linarith) (Real.exp_pos _).le
  have hc : (0 : ℝ) ≤ ((ParamsAdopted2.numStepsAdopted2 n : ℕ) : ℝ)
      * (2 * (4 * Real.exp (-((1 : ℝ) ^ 2 * (n : ℝ))))) := by positivity
  linarith

end Qrt

/-! ## 2. `κ − cqAt` in the three small quantities

`κ = (1/2 + 2rr)/mAt²` and `cqAt = 1/(2·MAt²·(1+δ)²)` both tend to `1/2`, and the budget's
numerator carries their difference times `K·h·dim ≈ 8·log n`.  README 29: the `log n` on one side
is paid for by `1/q` on the other, `q = ⁴√n`, and `log n ≤ 4q`.  Both lemmas are stated over bare
reals so that `nlinarith` sees only the arithmetic. -/

section KappaCq

/-- `1/mm² ≤ 1 + 8u`, hence `(1/2 + 2rr)/mm² ≤ 1/2 + 12u + 2rr`. -/
theorem kappa_upper {u mm rr : ℝ} (hmu : 1 - u ≤ mm) (hm2 : 1 / 2 ≤ mm) (hm1 : mm ≤ 1)
    (hu0 : 0 ≤ u) (hu : u ≤ 1 / 3) (hrr0 : 0 ≤ rr) (hrr : rr ≤ 1 / 2) :
    (1 / 2 + 2 * rr) / mm ^ 2 ≤ 1 / 2 + 12 * u + 2 * rr := by
  have hm0 : (0 : ℝ) < mm := by linarith
  have hinv : 1 / mm ^ 2 ≤ 1 + 8 * u := by
    have hpos : (0 : ℝ) ≤ 1 - u := by linarith
    have hsq : (1 - u) ^ 2 ≤ mm ^ 2 := by nlinarith [hmu, hpos]
    have hquad : (0 : ℝ) ≤ 6 - 15 * u + 8 * u ^ 2 := by
      nlinarith [sq_nonneg (u - 1 / 2), hu, hu0]
    have hone : (1 : ℝ) ≤ (1 + 8 * u) * (1 - u) ^ 2 := by nlinarith [mul_nonneg hu0 hquad]
    have hmul : (1 + 8 * u) * (1 - u) ^ 2 ≤ (1 + 8 * u) * mm ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by linarith)
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hsplit : (1 / 2 + 2 * rr) / mm ^ 2 = (1 / 2 + 2 * rr) * (1 / mm ^ 2) := by ring
  rw [hsplit]
  nlinarith [hinv, mul_nonneg hu0 (by linarith : (0 : ℝ) ≤ 1 / 2 - rr), hrr0, hu0]

/-- `1/(2Z²) ≥ 1/2 − 4u − 3δ` whenever `1 ≤ Z` and `Z² ≤ 1 + 8u + 6δ`. -/
theorem cq_of_Z {Z u dd : ℝ} (hZ1 : 1 ≤ Z) (hZsq : Z ^ 2 ≤ 1 + 8 * u + 6 * dd)
    (hu0 : 0 ≤ u) (hd0 : 0 ≤ dd) : 1 / 2 - 4 * u - 3 * dd ≤ 1 / (2 * Z ^ 2) := by
  have hZ0 : (0 : ℝ) < Z := by linarith
  have hZ2 : (1 : ℝ) ≤ Z ^ 2 := by nlinarith
  rw [le_div_iff₀ (by positivity)]
  nlinarith [hZsq, hZ2,
    mul_nonneg (by linarith : (0 : ℝ) ≤ 8 * u + 6 * dd) (by linarith : (0 : ℝ) ≤ Z ^ 2 - 1)]

/-- `1/2 − 1/(2·MM²(1+δ)²) ≤ 4u + 3δ` at `MM ≤ 1 + 2u`. -/
theorem cq_lower {u MM dd : ℝ} (hM1 : 1 ≤ MM) (hMu : MM ≤ 1 + 2 * u)
    (hu0 : 0 ≤ u) (hu : u ≤ 1 / 3) (hd0 : 0 ≤ dd) (hd : dd ≤ 1 / 4) :
    1 / 2 - 4 * u - 3 * dd ≤ 1 / (2 * MM ^ 2 * (1 + dd) ^ 2) := by
  have hZ1 : (1 : ℝ) ≤ MM * (1 + dd) := by nlinarith
  have hY : MM * (1 + dd) ≤ 1 + 2 * u + 5 * dd / 3 := by
    nlinarith [mul_le_mul_of_nonneg_right hMu (by linarith : (0 : ℝ) ≤ 1 + dd),
      mul_nonneg hd0 (by linarith : (0 : ℝ) ≤ 1 / 3 - u)]
  have hZsq : (MM * (1 + dd)) ^ 2 ≤ 1 + 8 * u + 6 * dd := by
    nlinarith [hY, hZ1, hu0, hd0, hu, hd]
  have hid : 2 * MM ^ 2 * (1 + dd) ^ 2 = 2 * (MM * (1 + dd)) ^ 2 := by ring
  rw [hid]
  exact cq_of_Z hZ1 hZsq hu0 hd0

end KappaCq

/-! ## 3. `driftCen` from above -/

section Cen

variable {n : ℕ}

/-- **`driftCen ≤ κ((1+ε)·K·c²·dim + (1+1/ε)(c₃η)²)`** — `TruncSumMean.integral_sum_sqTrunc_le`
on the truncated sum, the `(1+1/ε)` piece kept as it stands.  This is the companion of
`TruncSumMean.driftCen_ge`, in the direction `hbudget` needs. -/
theorem driftCen_le (hn : 3 ≤ n) {c κ ε c₃ η : ℝ} (hη : 0 < η) (hκ : 0 ≤ κ) (hε : 0 < ε)
    (K : ℕ) :
    DriftChargeTotal.driftCen (n := n) c η c₃ κ ε K
      ≤ κ * ((1 + ε) * ((K : ℝ) * (c ^ 2 * (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ)))
          + (1 + 1 / ε) * (c₃ * η) ^ 2) := by
  have hG := TruncSumMean.integral_sum_sqTrunc_le (n := n) hn (c := c) (cap := η ^ 2)
    (by positivity) K
  have h1 : (0 : ℝ) ≤ 1 + ε := by linarith
  have hmul := mul_le_mul_of_nonneg_left hG h1
  rw [DriftChargeTotal.driftCen]
  exact mul_le_mul_of_nonneg_left (by linarith) hκ

end Cen

/-! ## 4. `hS` with the bad event read at the cut index `K`

Report 99 §3 left this input open: `FinalDischarge2.hS_of_intWeight_wired` collapses the
`{k < τ}` failures against `wiredGood'`, whose count component sits at the **horizon** `N`, and
the tail side supplies the count only at `K < N`.  `GoodPathBounds.lt_tau_of_goodCut` closes it
directly: on `goodCut … K` the stopping time has not fired by `K`, hence not by any `k ≤ K`. -/

section HS

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι] {Ω : Type*} [MeasurableSpace Ω]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)} {P : Measure Ω} [IsProbabilityMeasure P]

/-- On `goodCut … K` the stopping time exceeds `K`, so it exceeds every `k ≤ K`. -/
theorem measureReal_compl_lt_tau_le_cut {r thr η r₀ c₃ pbad : ℝ}
    {Wacc : Ω → EuclideanSpace ℝ (UT n)} {N K k : ℕ} (hKN : K < N) (hk : k ≤ K)
    (hbad : P.real (GoodPathBounds.goodCut r Wacc ξ thr N η q W A₀ r₀ c₃ K)ᶜ ≤ pbad) :
    P.real {ω | k < tau q W A₀ ξ η r₀ c₃ N ω}ᶜ ≤ pbad := by
  refine le_trans (measureReal_mono ?_ (measure_ne_top P _)) hbad
  intro ω hω
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at hω ⊢
  intro hg
  have := GoodPathBounds.lt_tau_of_goodCut hg hKN
  omega

theorem sum_compl_lt_tau_le_cut {r thr η r₀ c₃ pbad : ℝ}
    {Wacc : Ω → EuclideanSpace ℝ (UT n)} {N K : ℕ} (hKN : K < N)
    (hbad : P.real (GoodPathBounds.goodCut r Wacc ξ thr N η q W A₀ r₀ c₃ K)ᶜ ≤ pbad) :
    ∑ k ∈ Finset.range K, P.real {ω | k < tau q W A₀ ξ η r₀ c₃ N ω}ᶜ ≤ (K : ℝ) * pbad := by
  calc ∑ k ∈ Finset.range K, P.real {ω | k < tau q W A₀ ξ η r₀ c₃ N ω}ᶜ
      ≤ ∑ _k ∈ Finset.range K, pbad :=
        Finset.sum_le_sum fun k hk =>
          measureReal_compl_lt_tau_le_cut hKN (by have := Finset.mem_range.1 hk; omega) hbad
    _ = (K : ℝ) * pbad := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **`hS` at the cut index.**  `GoodPathBounds.hS_of_intWeight` with the `{k < τ}` total
collapsed against `goodCut … K` — the event whose count the tail side does supply. -/
theorem hS_of_intWeight_cut {r thr η r₀ c₃ hstep Θ pbad : ℝ}
    {Wacc : Ω → EuclideanSpace ℝ (UT n)} {N K : ℕ} (hstep0 : 0 < hstep) (hKN : K < N)
    (hξ : ∀ j, Measurable (ξ j)) (hτ : Measurable (tau q W A₀ ξ η r₀ c₃ N))
    (hlight : ∑ y ∈ W, ContactIntegrated.intWeight P
        (fun k ω => (Chain.chain q W A₀ ξ k ω).2) hstep K y ≤ Θ)
    (hbad : P.real (GoodPathBounds.goodCut r Wacc ξ thr N η q W A₀ r₀ c₃ K)ᶜ ≤ pbad) :
    (K : ℝ) * (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) - Θ / hstep
        - (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) * ((K : ℝ) * pbad)
      ≤ ∑ k ∈ Finset.range K, ∫ ω,
          DriftStopped6.stoppedFreeDim q W A₀ ξ η r₀ c₃ N k ω ∂P := by
  have hbase := GoodPathBounds.hS_of_intWeight (q := q) (W := W) (A₀ := A₀) (ξ := ξ)
    (N := N) (m := K) hstep0 hξ hτ hlight
  have hsum := sum_compl_lt_tau_le_cut (q := q) (W := W) (A₀ := A₀) (ξ := ξ)
    (r := r) (thr := thr) (Wacc := Wacc) hKN hbad
  have hdim : (0 : ℝ) ≤ (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hsum hdim
  linarith

/-- **The `goodCut` failure is `failTotal`** — `goodPathCut`'s own union bound, extracted. -/
theorem goodCut_fail_le (hn : 3 ≤ n) {c₃ pcnt : ℝ} {K : ℕ}
    {q' : ι → EuclideanSpace ℝ (UT n)} {W' : Finset ι} {A₀' : EuclideanSpace ℝ (UT n)}
    (hcnt : (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))).real
      (StateInvariant4.countGood q' W' A₀' (ChainSetup.step (Submission.L10.cAdopted n)) K c₃)ᶜ
      ≤ pcnt) :
    (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))).real
        (GoodPathBounds.goodCut 1 (ChainSetup.coord 0)
          (ChainSetup.step (Submission.L10.cAdopted n)) (6 * 1 * 1 * Real.sqrt (n : ℝ))
          (ParamsAdopted2.numStepsAdopted2 n) (DriftStopped6.etaAdopted n)
          q' W' A₀' (DriftStopped6.r0Adopted n) c₃ K)ᶜ
      ≤ GoodPathBounds.failTotal n pcnt := by
  refine le_trans (GoodPathBounds.measureReal_compl_goodCut_le _ _ _ _ _ _ _ _) ?_
  rw [GoodPathBounds.failTotal]
  have h1 := GoodPathBounds.chainGood_failure (n := n) hn (r := 1) one_pos
  have h2 := GoodPathBounds.accGood_failure (q := q') (W := W') (A₀ := A₀') hn
  linarith

end HS

/-! ## 5. `hLb` at the cut index `K = N − 1`

`TruncSumMean.hLb_of_bounds` is pinned at `K = N` (report 99 §5(b)).  One step of the drift is
worth `c²·dim ≤ n²/n⁹ ≤ 1`, so the general-`K` form costs a constant. -/

section Lb

variable {n : ℕ}

/-- `N·X = T·dim·(1 − 50/n)` at the adopted parameters — `TruncSumMean.driftCen_ge_adopted`'s own
identity, extracted so a shorter horizon can use it. -/
theorem numSteps_mul_step_eq (hn : 3 ≤ n) :
    ((ParamsAdopted2.numStepsAdopted2 n : ℕ) : ℝ)
        * (Submission.L10.cAdopted n ^ 2 * (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ)
          - 100 * (Submission.L10.cAdopted n ^ 2) ^ 2 * ((Fintype.card (UT n) : ℝ)) ^ 2
            / DriftStopped6.etaAdopted n ^ 2)
      = ChainDrift.horizon n * (Fintype.card (UT n) : ℝ) * (1 - 50 / (n : ℝ)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hh0 : (0 : ℝ) < ParamsAdopted2.stepSizeAdopted2 n := TailSideSetup2.stepSizeAdopted2_pos hn
  have hD : (0 : ℝ) < (Fintype.card (UT n) : ℝ) := by
    have hpos : 0 < Fintype.card (UT n) := by
      rw [ChainWiring.card_UT]
      have hge : 12 ≤ n * (n + 1) := by nlinarith [hn]
      omega
    exact_mod_cast hpos
  have hfr : (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) = (Fintype.card (UT n) : ℝ) := by
    rw [finrank_euclideanSpace]
  have hNh := ParamsAdopted2.numStepsAdopted2_mul_stepSizeAdopted2 hn
  rw [TruncSumMean.cAdopted_sq hn, hfr, TruncSumMean.etaAdopted_sq hn]
  field_simp
  nlinarith [hNh, hh0, hD, hn0]

/-- One step of the drift is at most `1`: `c²·dim = h·card ≤ n²/n⁹`. -/
theorem step_mul_dim_le_one (hn : 2073600 ≤ n) :
    Submission.L10.cAdopted n ^ 2 * (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) ≤ 1 := by
  have hn3 : 3 ≤ n := by omega
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hfr : (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) = (Fintype.card (UT n) : ℝ) := by
    rw [finrank_euclideanSpace]
  have hd := Discharge.card_UT_le_sq (n := n) (by omega)
  have hd0 : (0 : ℝ) ≤ (Fintype.card (UT n) : ℝ) := Nat.cast_nonneg _
  have hh := ParamsAdopted2.stepSizeAdopted2_le hn3
  have hh0 : (0 : ℝ) ≤ ParamsAdopted2.stepSizeAdopted2 n := ParamsAdopted2.stepSizeAdopted2_nonneg hn3
  rw [TruncSumMean.cAdopted_sq hn3, hfr]
  have hmul : ParamsAdopted2.stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ)
      ≤ (1 / (n : ℝ) ^ 9) * (n : ℝ) ^ 2 := by
    apply mul_le_mul hh hd hd0 (by positivity)
  have hfin : (1 / (n : ℝ) ^ 9) * (n : ℝ) ^ 2 ≤ 1 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
    nlinarith [hnR, hn0, pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ (n : ℝ)) (by norm_num : 2 ≤ 9)]
  linarith

/-- **`log n/n ≤ 1/200`** — sharper than `AdoptedConstants95.log_ratio_le`, and what the
short-horizon `hLb` needs: `log n ≤ 4q` and `n = q⁴` give `log n/n ≤ 4/q³ ≤ 4/50 653`. -/
theorem log_div_le (hn : 2073600 ≤ n) : Real.log n / (n : ℝ) ≤ 1 / 200 := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  set qq := Real.sqrt (Real.sqrt (n : ℝ)) with hqdef
  have hq37 : (37 : ℝ) ≤ qq := WindowR.qrt_ge hn
  have hq0 : (0 : ℝ) < qq := by linarith
  have hq4 : qq ^ 4 = (n : ℝ) := WindowR.qrt_pow_four hn0.le
  have hlog : Real.log n ≤ 4 * qq := WindowR.log_le_four_qrt hn
  have hcube : 800 * qq ≤ qq ^ 4 := by
    have hq3 : (37 : ℝ) ^ 3 ≤ qq ^ 3 := pow_le_pow_left₀ (by norm_num) hq37 3
    have h4 : qq ^ 4 = qq ^ 3 * qq := by ring
    rw [h4]
    nlinarith [hq3, hq0]
  rw [div_le_div_iff₀ hn0 (by norm_num : (0 : ℝ) < 200)]
  linarith [hlog, hcube, hq4]

/-- **`driftCen ≥ 4·log n − 200·(log n/n) − 1/2` at `K = N − 1`.**  `TruncSumMean.driftCen_ge`
over the short horizon: the lost step is `c²·dim ≤ 1`, and `κ(1+ε) ≥ 1/2` does the rest.  This is
README 29's cancellation: the `+4·log n` here is what stands against `hLb`'s `−4·log n` and
against `−cqAt·c²·S` in the budget. -/
theorem driftCen_ge_cut (hn : 2073600 ≤ n) {κ ε c₃ : ℝ} {K : ℕ}
    (hκ : 1 / 2 ≤ κ) (hκ0 : 0 ≤ κ) (hε : 0 < ε)
    (hK : K + 1 = ParamsAdopted2.numStepsAdopted2 n) :
    4 * Real.log n - 200 * (Real.log n / (n : ℝ)) - 1 / 2
      ≤ DriftChargeTotal.driftCen (n := n) (Submission.L10.cAdopted n)
          (DriftStopped6.etaAdopted n) c₃ κ ε K := by
  have hn3 : 3 ≤ n := by omega
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hlog : (1 : ℝ) ≤ Real.log n := ChainDrift.log_pos_of_three hn3
  have hD : (0 : ℝ) < (Fintype.card (UT n) : ℝ) := by
    have hpos : 0 < Fintype.card (UT n) := by
      rw [ChainWiring.card_UT]
      have hge : 12 ≤ n * (n + 1) := by nlinarith [hn3]
      omega
    exact_mod_cast hpos
  have hcap : (0 : ℝ) < DriftStopped6.etaAdopted n ^ 2 := by
    rw [TruncSumMean.etaAdopted_sq hn3]
    have hh0 : (0 : ℝ) < ParamsAdopted2.stepSizeAdopted2 n :=
      TailSideSetup2.stepSizeAdopted2_pos hn3
    positivity
  have hbase := TruncSumMean.driftCen_ge (n := n) (c := Submission.L10.cAdopted n)
    (cap := DriftStopped6.etaAdopted n ^ 2) (κ := κ) (ε := ε) (c₃ := c₃)
    (η := DriftStopped6.etaAdopted n) hcap hκ0 hε K rfl
  have hNX := numSteps_mul_step_eq (n := n) hn3
  have hKR : ((ParamsAdopted2.numStepsAdopted2 n : ℕ) : ℝ) = (K : ℝ) + 1 := by
    rw [← hK]; push_cast; ring
  have hone := step_mul_dim_le_one (n := n) hn
  have hTd := TruncSumMean.horizon_mul_card_ge (n := n) hn3
  have hsmall := log_div_le (n := n) hn
  have hloss : (0 : ℝ) ≤ 1 - 50 / (n : ℝ) := by
    have : 50 / (n : ℝ) ≤ 1 := by rw [div_le_one hn0]; linarith
    linarith
  set XX := Submission.L10.cAdopted n ^ 2 * (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ)
      - 100 * (Submission.L10.cAdopted n ^ 2) ^ 2 * ((Fintype.card (UT n) : ℝ)) ^ 2
        / DriftStopped6.etaAdopted n ^ 2 with hXX
  have hXle : XX ≤ 1 := by
    rw [hXX]
    have : (0 : ℝ) ≤ 100 * (Submission.L10.cAdopted n ^ 2) ^ 2
        * ((Fintype.card (UT n) : ℝ)) ^ 2 / DriftStopped6.etaAdopted n ^ 2 := by positivity
    linarith
  have hAA : ChainDrift.horizon n * (Fintype.card (UT n) : ℝ) * (1 - 50 / (n : ℝ)) - 1
      ≤ (K : ℝ) * XX := by
    rw [← hNX, hKR]
    nlinarith [hXle]
  have hid : 8 * Real.log n * (1 - 50 / (n : ℝ))
      = 8 * Real.log n - 400 * (Real.log n / (n : ℝ)) := by field_simp; ring
  have hAge : 8 * Real.log n - 400 * (Real.log n / (n : ℝ))
      ≤ ChainDrift.horizon n * (Fintype.card (UT n) : ℝ) * (1 - 50 / (n : ℝ)) := by
    have h1 : 8 * Real.log n * (1 - 50 / (n : ℝ))
        ≤ ChainDrift.horizon n * (Fintype.card (UT n) : ℝ) * (1 - 50 / (n : ℝ)) :=
      mul_le_mul_of_nonneg_right hTd hloss
    linarith [hid.le, hid.ge]
  have hpos : (0 : ℝ) ≤ (K : ℝ) * XX := by linarith
  have hke : (1 : ℝ) / 2 ≤ κ * (1 + ε) := by nlinarith [hκ, hε]
  have hkap : (K : ℝ) * XX / 2 ≤ κ * ((1 + ε) * ((K : ℝ) * XX)) := by
    nlinarith [hke, hpos]
  linarith

/-- **`hLb` with the drift horizon one step short of `N`** — the two `4·log n` cancel. -/
theorem hLb_of_bounds_cut (hn : 2073600 ≤ n) {κ ε c₃ C' s' t : ℝ} {K : ℕ}
    (hκ : 1 / 2 ≤ κ) (hκ0 : 0 ≤ κ) (hε : 0 < ε) (hs' : 0 ≤ s') (ht : 0 ≤ t)
    (hK : K + 1 = ParamsAdopted2.numStepsAdopted2 n) (hC : 5 ≤ C') :
    ChainWiring.logDet (A0C n)
        - (DriftChargeTotal.driftCen (n := n) (Submission.L10.cAdopted n)
            (DriftStopped6.etaAdopted n) c₃ κ ε K + s') - t
      < C' - 4 * Real.log n := by
  have hcen := driftCen_ge_cut (n := n) (c₃ := c₃) hn hκ hκ0 hε hK
  have hA0 := AdoptedConstants95.logDet_A0C_le (n := n) (by omega)
  have hsmall := log_div_le (n := n) hn
  linarith

end Lb

/-! ## 6. The two thresholds at the per-dimension coefficient `B m = B₀/n²` -/

section Thresholds

variable {n : ℕ}

/-- `C3 n 1 (B₀/n²) α` is `TerminalRatio2`'s argument shape at
`b = (4e²(8 − 8/n²) + 4B₀)/n²`.  **The `n²` of the terminal term is cancelled by the `1/n²` of
the coefficient** — that is the whole content of brief 100. -/
theorem C3_eq_terminal_formB (hn : 2 ≤ n) {α B0 : ℝ} :
    TailAtStepR5W2.C3 n 1 (B0 / (n : ℝ) ^ 2) α
      = ((4 * Real.exp 2 * (8 - 8 / (n : ℝ) ^ 2) + 4 * B0) / (n : ℝ) ^ 2)
        * (Lemma43R.C1cR (a0C n) α n * (n : ℝ) ^ 2) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hne : ((n : ℝ)) ≠ 0 := ne_of_gt hn0
  rw [TailAtStepR5W2.C3, Lemma43R.C1R]
  field_simp

/-- **The combined threshold is `n`-free** at `B m = B₀/n²`. -/
theorem thetaTight_combB_le {p : ℕ} {α B0 : ℝ} (hn : 2073600 ≤ n) (hα : 0 < α) (hB0 : 0 ≤ B0)
    (hdef : (n : ℝ) * (α * Real.sqrt n / 2) ≤ 1 / 4)
    (halpha : α ^ n * ((p ^ (n - 1) : ℕ) : ℝ) = Section5.kappa n)
    (hp : 1 ≤ (p : ℝ)) (hpn : 1 ≤ ((p ^ (n - 1) : ℕ) : ℝ)) (hppos : 1 < (p : ℝ) ^ n) :
    ThetaTight.thetaTight p n (TailAtStepR5W2.C3 n 1 (B0 / (n : ℝ) ^ 2) α)
      ≤ 3308 * (32 * Real.exp 2 + 4 * B0) := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have height : (0 : ℝ) < 8 - 8 / (n : ℝ) ^ 2 := Lemma43R.eight_sub_pos (by omega)
  have hex0 : (0 : ℝ) < Real.exp 2 := Real.exp_pos 2
  have hb0 : (0 : ℝ) ≤ (4 * Real.exp 2 * (8 - 8 / (n : ℝ) ^ 2) + 4 * B0) / (n : ℝ) ^ 2 := by
    have hnum : (0 : ℝ) ≤ 4 * Real.exp 2 * (8 - 8 / (n : ℝ) ^ 2) + 4 * B0 := by nlinarith
    positivity
  rw [C3_eq_terminal_formB (by omega)]
  refine le_trans (TerminalRatio2.thetaTight_terminal_le' (p := p) hn hα hb0 hdef halpha
    hp hpn hppos) ?_
  have hid : 4 * ((4 * Real.exp 2 * (8 - 8 / (n : ℝ) ^ 2) + 4 * B0) / (n : ℝ) ^ 2) * 827
        * (n : ℝ) ^ 2
      = 3308 * (4 * Real.exp 2 * (8 - 8 / (n : ℝ) ^ 2) + 4 * B0) := by
    field_simp; ring
  rw [hid]
  have hle8 : 8 - 8 / (n : ℝ) ^ 2 ≤ 8 := by
    have : (0 : ℝ) ≤ 8 / (n : ℝ) ^ 2 := by positivity
    linarith
  nlinarith [hex0, hle8]

/-- **The count ratio, with the `q³` kept.**  `c₃'' = n²·q³`, so a terminal weight `θT ≤ Kc·n²`
gives a Markov ratio `2·Kc/q³` — the `q³` is what makes `log n · pcnt` bounded. -/
theorem count_ratio_q {θT Kc : ℝ} (hn : 2073600 ≤ n) (_hKc : 0 ≤ Kc)
    (hθ : θT ≤ Kc * (n : ℝ) ^ 2) :
    (2 * θT + 0) / DriftStopped6c.c3Adopted'' n
      ≤ 2 * Kc / Real.sqrt (Real.sqrt (n : ℝ)) ^ 3 := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hq37 : (37 : ℝ) ≤ Real.sqrt (Real.sqrt (n : ℝ)) := WindowR.qrt_ge hn
  have hq0 : (0 : ℝ) < Real.sqrt (Real.sqrt (n : ℝ)) := by linarith
  have hq3 : (0 : ℝ) < Real.sqrt (Real.sqrt (n : ℝ)) ^ 3 := by positivity
  rw [DriftStopped6c.c3Adopted'', div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right hθ hq3.le]

/-- **`T·dim ≤ 16·log n`** — the companion of `TruncSumMean.horizon_mul_card_ge`. -/
theorem horizon_mul_card_le (hn : 2073600 ≤ n) :
    ChainDrift.horizon n * (Fintype.card (UT n) : ℝ) ≤ 16 * Real.log n := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hlog : (1 : ℝ) ≤ Real.log n := ChainDrift.log_pos_of_three (by omega)
  have hd := Discharge.card_UT_le_sq (n := n) (by omega)
  rw [ChainDrift.horizon]
  have hstep : 16 * Real.log n / (n : ℝ) ^ 2 * (Fintype.card (UT n) : ℝ)
      ≤ 16 * Real.log n / (n : ℝ) ^ 2 * (n : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_left hd (by positivity)
  have hid : 16 * Real.log n / (n : ℝ) ^ 2 * (n : ℝ) ^ 2 = 16 * Real.log n := by
    field_simp
  linarith [hid.le, hid.ge]

/-! ### The failure total with an inverse-linear remainder

`FailTotalBound99.failTotal_le` gives `failTotal ≤ pcnt + 10⁻³`, and the budget's `pbad` term is
multiplied by `K·c²·dim ≈ 8·log n`.  A flat `10⁻³` would leave a `log n` uncancelled (README 29);
`10⁻³/n` does not.  The margin is the same 29 orders: `173·20²⁰ ≤ 10⁵⁴/1000`. -/

theorem const_le_inv (hn : 2073600 ≤ n) :
    173 * (n : ℝ) ^ 10 * (20 ^ 20 / (n : ℝ) ^ 20) ≤ 1 / (1000 * (n : ℝ)) := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hid : 173 * (n : ℝ) ^ 10 * (20 ^ 20 / (n : ℝ) ^ 20) = 173 * 20 ^ 20 / (n : ℝ) ^ 10 := by
    field_simp
  rw [hid, div_le_div_iff₀ (by positivity) (by positivity)]
  have hbig : ((1000000 : ℝ)) ^ 9 ≤ (n : ℝ) ^ 9 :=
    pow_le_pow_left₀ (by norm_num) (by linarith) 9
  have hpow : (n : ℝ) ^ 10 = (n : ℝ) ^ 9 * (n : ℝ) := by ring
  have hval : (173 : ℝ) * 20 ^ 20 * 1000 ≤ (1000000 : ℝ) ^ 9 := by norm_num
  rw [hpow]
  nlinarith [hbig, hn0, hval]

/-- **`failTotal n pcnt ≤ pcnt + 1/(1000·n)`.** -/
theorem failTotal_le_inv (hn : 2073600 ≤ n) (pcnt : ℝ) :
    GoodPathBounds.failTotal n pcnt ≤ pcnt + 1 / (1000 * (n : ℝ)) := by
  have hn1 : 1 ≤ n := by omega
  have hE0 : (0 : ℝ) ≤ Real.exp (-(n : ℝ)) := (Real.exp_pos _).le
  have hEb : Real.exp (-(n : ℝ)) ≤ 20 ^ 20 / (n : ℝ) ^ 20 := ExpDecay99.exp_neg_nat_le hn1
  have hpoly := FailTotalBound99.poly_le hn1
  have hstep1 : ((33 * (n : ℝ) ^ 9 * Real.log n + 4)
        + 8 * ((ParamsAdopted2.numStepsAdopted2 n : ℕ) : ℝ)) * Real.exp (-(n : ℝ))
      ≤ (173 * (n : ℝ) ^ 10) * Real.exp (-(n : ℝ)) :=
    mul_le_mul_of_nonneg_right hpoly hE0
  have hstep2 : (173 * (n : ℝ) ^ 10) * Real.exp (-(n : ℝ))
      ≤ (173 * (n : ℝ) ^ 10) * (20 ^ 20 / (n : ℝ) ^ 20) :=
    mul_le_mul_of_nonneg_left hEb (by positivity)
  have hstep3 := const_le_inv hn
  rw [GoodPathBounds.failTotal]
  simp only [one_pow, one_mul]
  linarith

/-- **The threshold at `B₀ = 140`, as a number**: `3308·(32e² + 560) ≤ 2.64·10⁶`. -/
theorem thetaTight_le_2800000 {p : ℕ} {α : ℝ} (hn : 2073600 ≤ n) (hα : 0 < α)
    (hdef : (n : ℝ) * (α * Real.sqrt n / 2) ≤ 1 / 4)
    (halpha : α ^ n * ((p ^ (n - 1) : ℕ) : ℝ) = Section5.kappa n)
    (hp : 1 ≤ (p : ℝ)) (hpn : 1 ≤ ((p ^ (n - 1) : ℕ) : ℝ)) (hppos : 1 < (p : ℝ) ^ n) :
    ThetaTight.thetaTight p n (TailAtStepR5W2.C3 n 1 (140 / (n : ℝ) ^ 2) α) ≤ 2800000 := by
  have h := thetaTight_combB_le (n := n) (p := p) (α := α) (B0 := 140) hn hα (by norm_num)
    hdef halpha hp hpn hppos
  have hex : Real.exp 2 ≤ 7.4 := ThetaIntegrated99.exp_two_le
  linarith

end Thresholds

/-! ## 7. The budget's numerator and the shortfall, as bare arithmetic -/

section NumArith

/-- **The numerator, bounded term by term.**  `G = K·c²·dim ≤ 64q` carries a `log n`, so the gap
`κ(1+ε) − cqAt ≤ 200/q` is what keeps `(κ(1+ε) − cqAt)·G` bounded; likewise `q·pbad ≤ 15`
against `cqAt·G·pbad` (README 29, twice). -/
theorem num_le_const {kap eps cq G Th pbad Ea CB sp tt ss qv xx cen : ℝ}
    (hqv : 37 ≤ qv) (heps : eps = 1 / qv)
    (hcen : cen ≤ kap * ((1 + eps) * G + (1 + 1 / eps) * xx))
    (hgap : kap * (1 + eps) - cq ≤ 200 / qv)
    (hG0 : 0 ≤ G) (hG : G ≤ 64 * qv)
    (_hkap0 : 0 ≤ kap) (hkap : kap ≤ 5)
    (hx0 : 0 ≤ xx) (hx : xx ≤ 4 / qv ^ 2)
    (_hcq0 : 0 ≤ cq) (hcqh : cq ≤ 1 / 2)
    (hTh0 : 0 ≤ Th) (hTh : Th ≤ 2800000)
    (hpbad0 : 0 ≤ pbad) (hpb : qv * pbad ≤ 16)
    (hEa : Ea ≤ 1) (hCB : CB ≤ 1) (hsp : sp ≤ 1) (htt : tt ≤ 1) (hss : ss ≤ 20) :
    cen - cq * G + cq * Th + cq * G * pbad + Ea + CB + sp + tt + ss ≤ 1450000 := by
  have hqv0 : (0 : ℝ) < qv := by linarith
  have hring : kap * ((1 + eps) * G + (1 + 1 / eps) * xx) - cq * G
      = (kap * (1 + eps) - cq) * G + kap * (1 + 1 / eps) * xx := by ring
  have hA : cen - cq * G ≤ (kap * (1 + eps) - cq) * G + kap * (1 + 1 / eps) * xx := by
    rw [← hring]; linarith
  have h2 : (kap * (1 + eps) - cq) * G ≤ 200 / qv * G := mul_le_mul_of_nonneg_right hgap hG0
  have h3 : 200 / qv * G ≤ 200 / qv * (64 * qv) := mul_le_mul_of_nonneg_left hG (by positivity)
  have h4 : 200 / qv * (64 * qv) = 12800 := by field_simp; ring
  have heinv : 1 / eps = qv := by rw [heps]; field_simp
  have h5 : kap * (1 + 1 / eps) * xx ≤ 2 := by
    rw [heinv]
    have hq1 : (0 : ℝ) ≤ 1 + qv := by linarith
    have hs1 : kap * (1 + qv) ≤ 5 * (1 + qv) := by nlinarith
    have hs2 : kap * (1 + qv) * xx ≤ 5 * (1 + qv) * xx := mul_le_mul_of_nonneg_right hs1 hx0
    have hs3 : 5 * (1 + qv) * xx ≤ 5 * (1 + qv) * (4 / qv ^ 2) :=
      mul_le_mul_of_nonneg_left hx (by linarith)
    have hs4 : 5 * (1 + qv) * (4 / qv ^ 2) ≤ 2 := by
      rw [show (5 : ℝ) * (1 + qv) * (4 / qv ^ 2) = 20 * (1 + qv) / qv ^ 2 by ring,
        div_le_iff₀ (by positivity)]
      nlinarith [hqv, hqv0]
    linarith
  have h7 : cq * Th ≤ 1400000 := by
    nlinarith [mul_le_mul hcqh hTh hTh0 (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have h8 : cq * G * pbad ≤ 512 := by
    have hb1 : cq * G ≤ 1 / 2 * (64 * qv) := mul_le_mul hcqh hG hG0 (by norm_num)
    have hb2 : cq * G * pbad ≤ 1 / 2 * (64 * qv) * pbad :=
      mul_le_mul_of_nonneg_right hb1 hpbad0
    nlinarith [hb2, hpb]
  linarith [h4.le, h4.ge]

/-- The shortfall total at `t' = s' = 1`, with both variance terms below `1`. -/
theorem shortfall_le_twenty {v w kp : ℝ} (_hv0 : 0 ≤ v) (hv : v ≤ 1) (_hw0 : 0 ≤ w)
    (hw : w ≤ 1) (hkp0 : 0 ≤ kp) (hkp : kp ≤ 6) :
    v / (4 * 1) + 1 + (2 * kp ^ 2 * w + 2 * v) / (4 * 1) ≤ 20 := by
  have hk2 : kp ^ 2 ≤ 36 := by nlinarith
  have hkw : kp ^ 2 * w ≤ 36 := by nlinarith [sq_nonneg kp]
  linarith

/-- `q ≤ q⁴` for `q ≥ 37`. -/
theorem qrt_le_self {qv nn : ℝ} (h37 : 37 ≤ qv) (h4 : qv ^ 4 = nn) : qv ≤ nn := by
  have h3 : (1 : ℝ) ≤ qv ^ 3 := one_le_pow₀ (by linarith)
  nlinarith [h3, h37, h4.le, h4.ge]

/-- `η/m ≤ 2/q` from `η ≤ 1/q` and `m ≥ 1/2`. -/
theorem delta_le_two_div {et mm qv : ℝ} (hq0 : 0 < qv) (het : et ≤ 1 / qv) (hmm : 1 / 2 ≤ mm) :
    et / mm ≤ 2 / qv := by
  have h1 : et * qv ≤ 1 / qv * qv := mul_le_mul_of_nonneg_right het hq0.le
  have h2 : 1 / qv * qv = 1 := by field_simp
  rw [div_le_div_iff₀ (by linarith) hq0]
  linarith [h1, h2.le, h2.ge]

/-- `2·rr = 4η + 4c₃η ≤ 12/q`. -/
theorem rr_le_twelve {c3 et qv : ℝ} (hq0 : 0 < qv) (het : et ≤ 1 / qv)
    (hce : c3 * et ≤ 2 / qv) : 2 * (2 * (1 + c3) * et) ≤ 12 / qv := by
  have hqne : qv ≠ 0 := ne_of_gt hq0
  have hexp : 2 * (2 * (1 + c3) * et) = 4 * et + 4 * (c3 * et) := by ring
  have h4 : (12 : ℝ) / qv = 4 * (1 / qv) + 4 * (2 / qv) := by field_simp; ring
  rw [hexp, h4]
  linarith

/-- `(1+c₃)η ≤ rr·m` at `rr = 2(1+c₃)η` and `m ≥ 1/2`. -/
theorem rm_ge {c3 et mm : ℝ} (hnn : 0 ≤ (1 + c3) * et) (hmm : 1 / 2 ≤ mm) :
    (1 + c3) * et ≤ 2 * (1 + c3) * et * mm := by
  nlinarith [mul_nonneg hnn (by linarith : (0 : ℝ) ≤ 2 * mm - 1)]

/-- `20000/q² ≤ 15` at `q ≥ 37`. -/
theorem twenty_k_div_sq_le {qv : ℝ} (h37 : 37 ≤ qv) : 20000 / qv ^ 2 ≤ 15 := by
  have hq0 : (0 : ℝ) < qv := by linarith
  rw [div_le_iff₀ (by positivity)]
  nlinarith [h37, hq0]

/-- **The gap, as bare arithmetic**: `κ(1+ε) − cq ≤ 183·(1/q) ≤ 200·(1/q)`. -/
theorem gap_le {kap cq u rr dd eps iq : ℝ} (hiq : 0 ≤ iq)
    (hkapup : kap ≤ 1 / 2 + 12 * u + 2 * rr) (hcqlow : 1 / 2 - 4 * u - 3 * dd ≤ cq)
    (hu : u ≤ 10 * iq) (hrr : 2 * rr ≤ 12 * iq) (hdd : dd ≤ 2 * iq)
    (hkeps : kap * eps ≤ 5 * iq) : kap * (1 + eps) - cq ≤ 200 * iq := by
  have hexp : kap * (1 + eps) = kap + kap * eps := by ring
  rw [hexp]
  linarith

/-- **The numerator identity.**  `S = K·dim − Θ/h − dim·(K·pbad)` and
`L = logDet A₀ − (driftCen + 1) − 1`, so `driftRHS_acc − L + 20` is the term list
`num_le_const` bounds. -/
theorem rhs_identity {ld cq h dim KK Th pb Ea CB cen : ℝ} (hh : h ≠ 0) :
    ld - cq * h * (KK * dim - Th / h - dim * (KK * pb)) + (Ea + CB)
        - (ld - (cen + 1) - 1) + 20
      = cen - cq * (KK * (h * dim)) + cq * Th + cq * (KK * (h * dim)) * pb
        + Ea + CB + 1 + 1 + 20 := by
  field_simp
  ring

/-- `κ(1+ε) ≤ 6` at `κ ≤ 5`, `ε ≤ 1/5`. -/
theorem kp_le_six {kap eps : ℝ} (hkap0 : 0 ≤ kap) (hkap : kap ≤ 5) (_heps0 : 0 ≤ eps)
    (heps : eps ≤ 1 / 5) : kap * (1 + eps) ≤ 6 := by nlinarith

/-- `20000/q³ ≤ 0.396` at `q ≥ 37` (measured `0.394 8`; the ceiling is chosen above it). -/
theorem twenty_k_div_cube_le {qv : ℝ} (h37 : 37 ≤ qv) : 2 * 10000 / qv ^ 3 ≤ 396 / 1000 := by
  have hq0 : (0 : ℝ) < qv := by linarith
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  have hq3 : (37 : ℝ) ^ 3 ≤ qv ^ 3 := pow_le_pow_left₀ (by norm_num) h37 3
  nlinarith [hq3]

end NumArith

/-! ## 8. The two variance terms of the shortfall, at the adopted parameters -/

section VW

variable {n : ℕ}

/-- `K·c²·(n/m²) ≤ 1`: `K·h ≤ T = 16 log n/n²`, `n/m² ≤ 4n`, and `log n/n ≤ 1/200`. -/
theorem vterm_le (hn : 2073600 ≤ n) {K : ℕ} {mm : ℝ}
    (hK : (K : ℝ) ≤ ((ParamsAdopted2.numStepsAdopted2 n : ℕ) : ℝ)) (hmm : 1 / 2 ≤ mm) :
    (K : ℝ) * (Submission.L10.cAdopted n ^ 2 * ((n : ℝ) / mm ^ 2)) ≤ 1 := by
  have hn3 : 3 ≤ n := by omega
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
  have hh0 : (0 : ℝ) ≤ ParamsAdopted2.stepSizeAdopted2 n :=
    (TailSideSetup2.stepSizeAdopted2_pos hn3).le
  have hNh := ParamsAdopted2.numStepsAdopted2_mul_stepSizeAdopted2 hn3
  have hKh : (K : ℝ) * ParamsAdopted2.stepSizeAdopted2 n ≤ ChainDrift.horizon n := by
    rw [← hNh]; nlinarith [hK, hh0]
  have hm0 : (0 : ℝ) < mm := by linarith
  have hmsq : (1 : ℝ) / 4 ≤ mm ^ 2 := by nlinarith [hmm]
  have hratio : (n : ℝ) / mm ^ 2 ≤ 4 * (n : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hmsq, hn0, mul_nonneg (by linarith : (0 : ℝ) ≤ mm ^ 2 - 1 / 4) hn0.le]
  have hrat0 : (0 : ℝ) ≤ (n : ℝ) / mm ^ 2 := by positivity
  have hT0 : (0 : ℝ) ≤ ChainDrift.horizon n := by
    rw [ChainDrift.horizon]
    have : (1 : ℝ) ≤ Real.log n := ChainDrift.log_pos_of_three hn3
    positivity
  have hassoc : (K : ℝ) * (Submission.L10.cAdopted n ^ 2 * ((n : ℝ) / mm ^ 2))
      = ((K : ℝ) * ParamsAdopted2.stepSizeAdopted2 n) * ((n : ℝ) / mm ^ 2) := by
    rw [TruncSumMean.cAdopted_sq hn3]; ring
  rw [hassoc]
  have hstep : ((K : ℝ) * ParamsAdopted2.stepSizeAdopted2 n) * ((n : ℝ) / mm ^ 2)
      ≤ ChainDrift.horizon n * (4 * (n : ℝ)) :=
    mul_le_mul hKh hratio hrat0 hT0
  have hfin : ChainDrift.horizon n * (4 * (n : ℝ)) = 64 * (Real.log n / (n : ℝ)) := by
    rw [ChainDrift.horizon]; field_simp; ring
  have hsmall := log_div_le (n := n) hn
  linarith [hfin.le, hfin.ge]

/-- `K·(η²/2)² ≤ 1`: `η²/2 = h·card·n`, `h ≤ n⁻⁹`, `card ≤ n²`, and `K·h ≤ 16 log n/n²`. -/
theorem wterm_le (hn : 2073600 ≤ n) {K : ℕ}
    (hK : (K : ℝ) ≤ ((ParamsAdopted2.numStepsAdopted2 n : ℕ) : ℝ)) :
    (K : ℝ) * (DriftStopped6.etaAdopted n ^ 2 / 2) ^ 2 ≤ 1 := by
  have hn3 : 3 ≤ n := by omega
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
  have hh0 : (0 : ℝ) ≤ ParamsAdopted2.stepSizeAdopted2 n :=
    (TailSideSetup2.stepSizeAdopted2_pos hn3).le
  have hh := ParamsAdopted2.stepSizeAdopted2_le hn3
  have hd := Discharge.card_UT_le_sq (n := n) (by omega)
  have hd0 : (0 : ℝ) ≤ (Fintype.card (UT n) : ℝ) := Nat.cast_nonneg _
  have hNh := ParamsAdopted2.numStepsAdopted2_mul_stepSizeAdopted2 hn3
  have hKh : (K : ℝ) * ParamsAdopted2.stepSizeAdopted2 n ≤ ChainDrift.horizon n := by
    rw [← hNh]; nlinarith [hK, hh0]
  have hT0 : (0 : ℝ) ≤ ChainDrift.horizon n := by
    rw [ChainDrift.horizon]
    have : (1 : ℝ) ≤ Real.log n := ChainDrift.log_pos_of_three hn3
    positivity
  have hlogn : Real.log n ≤ (n : ℝ) := by
    have h := Real.log_le_sub_one_of_pos hn0; linarith
  have hid : (K : ℝ) * (DriftStopped6.etaAdopted n ^ 2 / 2) ^ 2
      = ((K : ℝ) * ParamsAdopted2.stepSizeAdopted2 n)
        * (ParamsAdopted2.stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ) ^ 2 * (n : ℝ) ^ 2) := by
    rw [TruncSumMean.etaAdopted_sq hn3]; ring
  rw [hid]
  have hrest : ParamsAdopted2.stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ) ^ 2 * (n : ℝ) ^ 2
      ≤ (1 / (n : ℝ) ^ 9) * ((n : ℝ) ^ 2) ^ 2 * (n : ℝ) ^ 2 := by
    have hc2 : (Fintype.card (UT n) : ℝ) ^ 2 ≤ ((n : ℝ) ^ 2) ^ 2 := by nlinarith [hd, hd0]
    have h1 : ParamsAdopted2.stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ) ^ 2
        ≤ (1 / (n : ℝ) ^ 9) * ((n : ℝ) ^ 2) ^ 2 :=
      mul_le_mul hh hc2 (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  have hrest0 : (0 : ℝ) ≤ ParamsAdopted2.stepSizeAdopted2 n
      * (Fintype.card (UT n) : ℝ) ^ 2 * (n : ℝ) ^ 2 := by positivity
  have hprod : ((K : ℝ) * ParamsAdopted2.stepSizeAdopted2 n)
        * (ParamsAdopted2.stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ) ^ 2 * (n : ℝ) ^ 2)
      ≤ ChainDrift.horizon n * ((1 / (n : ℝ) ^ 9) * ((n : ℝ) ^ 2) ^ 2 * (n : ℝ) ^ 2) :=
    mul_le_mul hKh hrest hrest0 hT0
  have hval : ChainDrift.horizon n * ((1 / (n : ℝ) ^ 9) * ((n : ℝ) ^ 2) ^ 2 * (n : ℝ) ^ 2)
      = 16 * Real.log n / (n : ℝ) ^ 5 := by
    rw [ChainDrift.horizon]; field_simp
  have hlast : 16 * Real.log n / (n : ℝ) ^ 5 ≤ 1 := by
    have hn4 : (16 : ℝ) ≤ (n : ℝ) ^ 4 := by
      have h24 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2)
        (show (2 : ℝ) ≤ (n : ℝ) by linarith) 4
      norm_num at h24
      linarith
    have hpow : (n : ℝ) ^ 5 = (n : ℝ) ^ 4 * (n : ℝ) := by ring
    rw [div_le_one (by positivity), hpow]
    nlinarith [hlogn, hn0, mul_nonneg (by linarith : (0 : ℝ) ≤ (n : ℝ) ^ 4 - 16) hn0.le]
  linarith [hval.le, hval.ge]

end VW

/-! ## 9. The composition: `A = 1`, `B m = 140/(m+1)²`, `C' = 10⁷`, `K = N − 1` -/

/-- **The per-dimension terminal coefficient.**  Report 74 §4's design had the terminal weight's
coefficient proportional to `1/n²`; the frozen chain froze it as a real, which is what put an `n²`
into the integrated contact threshold (report 99 §2). -/
noncomputable def Bfam (m : ℕ) : ℝ := 140 / ((m + 1 : ℕ) : ℝ) ^ 2

theorem Bfam_nonneg (m : ℕ) : 0 ≤ Bfam m := by rw [Bfam]; positivity

/-- **The cut index**: one step short of the horizon. -/
noncomputable def Kcut (m : ℕ) : ℕ := ParamsAdopted2.numStepsAdopted2 (m + 1) - 1

theorem Kcut_lt (m : ℕ) (hm : Threshold2.n₁ ≤ m) :
    Kcut m < ParamsAdopted2.numStepsAdopted2 (m + 1) := by
  have hm1 : 2073600 ≤ m + 1 := by
    have h2 : 2073600 ≤ m := by simpa [Threshold2.n₁] using hm
    omega
  have := three_le_numStepsAdopted2 (n := m + 1) (by omega)
  rw [Kcut]; omega

theorem Kcut_succ (m : ℕ) (hm : Threshold2.n₁ ≤ m) :
    Kcut m + 1 = ParamsAdopted2.numStepsAdopted2 (m + 1) := by
  have hm1 : 2073600 ≤ m + 1 := by
    have h2 : 2073600 ≤ m := by simpa [Threshold2.n₁] using hm
    omega
  have := three_le_numStepsAdopted2 (n := m + 1) (by omega)
  rw [Kcut]; omega

/-- The shortfall's free parameter `rr`, chosen so that `rr·mAt ≥ (1+c₃)·η` with `mAt ≥ 1/2`. -/
noncomputable def rrAt (n : ℕ) : ℝ :=
  2 * (1 + DriftStopped6c.c3Adopted'' n) * DriftStopped6.etaAdopted n

/-- The drift's free parameter `ε = 1/q`: `κ·ε·K·c²·dim ≤ 5·64 = 320` and
`(1+1/ε)(c₃η)² ≤ 2` are both bounded (README 29). -/
noncomputable def epsAt (n : ℕ) : ℝ := 1 / Real.sqrt (Real.sqrt (n : ℝ))

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **The challenge statement, with no hypotheses.** -/
theorem klartag_packing_final :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      let V := EuclideanSpace ℝ (Fin (n + 1))
      ∃ φ : V →ₗ[ℝ] V, let E := φ '' Metric.ball (0 : V) 1
        (MeasureTheory.volume E : EReal) = c * n ^ 2 ∧
        {v ∈ E | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} := by
  refine Theorem2R5.klartag_packing_final_lightB (A := 1) (B := Bfam) one_pos Bfam_nonneg
    (C' := 10000000) (K := Kcut) Kcut_lt ?_
  intro m hm p hp hp0 α hα hn3 hraw hnd g hlight
  -- ### thresholds and indices
  have hm1 : 2073600 ≤ m + 1 := by
    have h2 : 2073600 ≤ m := by simpa [Threshold2.n₁] using hm
    omega
  have hnR : (2073600 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast hm1
  have hn0 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by linarith
  have hKlt := Kcut_lt m hm
  have hKsucc := Kcut_succ m hm
  have hN1 : 1 ≤ ParamsAdopted2.numStepsAdopted2 (m + 1) := by omega
  have hKleN : Kcut m ≤ ParamsAdopted2.numStepsAdopted2 (m + 1) := by omega
  have hKle : (Kcut m : ℝ) ≤ ((ParamsAdopted2.numStepsAdopted2 (m + 1) : ℕ) : ℝ) := by
    exact_mod_cast hKleN
  -- ### the quarter root
  have hq37 : (37 : ℝ) ≤ Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ)) := WindowR.qrt_ge hm1
  have hq0 : (0 : ℝ) < Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ)) := by linarith
  have hq4 : Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ)) ^ 4 = ((m + 1 : ℕ) : ℝ) :=
    WindowR.qrt_pow_four hn0.le
  have hqle : Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ)) ≤ ((m + 1 : ℕ) : ℝ) :=
    qrt_le_self hq37 hq4
  -- ### the adopted constants
  have hc30 := DriftStopped6c.c3Adopted''_nonneg (m + 1)
  have hc3pos := DriftStopped6c.c3Adopted''_pos (n := m + 1) (by omega)
  have hc3eta := DriftStopped6c.c3Adopted''_eta_le hm1
  have hc3q := DriftStopped6c.c3eta_le hm1
  have hη0 : (0 : ℝ) ≤ DriftStopped6.etaAdopted (m + 1) := DriftStopped7.etaAdopted_nonneg
  have hηq := eta_le_qrt hm1
  have hr00 : (0 : ℝ) ≤ DriftStopped6.r0Adopted (m + 1) := DriftStopped7.r0Adopted_nonneg
  have hr0q := r0_le_qrt hm1
  have hmhalf := GoodPathBounds.half_le_mAt hm1 hc3eta
  have hmone := AdoptedConstants95.mAt_le_one (n := m + 1) (by omega) hc30
  have hMone := GoodPathBounds.one_le_MAt hm1 hc30
  have hcq0 := GoodPathBounds.cqAt_nonneg hm1 hc3eta hc30
  have hcqh := DriftStopped6b.cqAt_le_half hm1 hc30 hc3eta
  have ha01 := DriftStopped7.one_le_a0C (n := m + 1) (by omega)
  have ha0u := AdoptedConstants95.a0C_sub_one_le (n := m + 1) (by omega)
  have h4r0 := AdoptedConstants95.four_div_le_r0 (n := m + 1) (by omega)
  -- `u = r₀ + c₃η`, in `1/q`
  have hu0 : (0 : ℝ) ≤ DriftStopped6.r0Adopted (m + 1)
      + DriftStopped6c.c3Adopted'' (m + 1) * DriftStopped6.etaAdopted (m + 1) := by positivity
  have huq : DriftStopped6.r0Adopted (m + 1)
      + DriftStopped6c.c3Adopted'' (m + 1) * DriftStopped6.etaAdopted (m + 1)
      ≤ 10 / Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ)) := by
    have : (8 : ℝ) / Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ))
        + 2 / Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ))
        = 10 / Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ)) := by ring
    linarith [hr0q, hc3q, this.le, this.ge]
  have hq10 : (10 : ℝ) / Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ)) ≤ 1 / 3 := by
    rw [div_le_div_iff₀ hq0 (by norm_num)]; linarith
  have hu3 : DriftStopped6.r0Adopted (m + 1)
      + DriftStopped6c.c3Adopted'' (m + 1) * DriftStopped6.etaAdopted (m + 1) ≤ 1 / 3 := by
    linarith
  have hmAtEq : GoodPathBounds.mAt (m + 1) (DriftStopped6c.c3Adopted'' (m + 1))
      = a0C (m + 1) - (DriftStopped6.r0Adopted (m + 1)
        + DriftStopped6c.c3Adopted'' (m + 1) * DriftStopped6.etaAdopted (m + 1)) :=
    rfl
  have hMAtEq : GoodPathBounds.MAt (m + 1) (DriftStopped6c.c3Adopted'' (m + 1))
      = a0C (m + 1) + (DriftStopped6.r0Adopted (m + 1)
        + DriftStopped6c.c3Adopted'' (m + 1) * DriftStopped6.etaAdopted (m + 1)) :=
    rfl
  have hmm : (1 : ℝ) / 2 ≤ a0C (m + 1) - (DriftStopped6.r0Adopted (m + 1)
      + DriftStopped6c.c3Adopted'' (m + 1) * DriftStopped6.etaAdopted (m + 1)) := by
    rw [hmAtEq] at hmhalf; exact hmhalf
  have hmm1 : a0C (m + 1) - (DriftStopped6.r0Adopted (m + 1)
      + DriftStopped6c.c3Adopted'' (m + 1) * DriftStopped6.etaAdopted (m + 1)) ≤ 1 := by
    rw [hmAtEq] at hmone; exact hmone
  have hmu : 1 - (DriftStopped6.r0Adopted (m + 1)
        + DriftStopped6c.c3Adopted'' (m + 1) * DriftStopped6.etaAdopted (m + 1))
      ≤ a0C (m + 1) - (DriftStopped6.r0Adopted (m + 1)
        + DriftStopped6c.c3Adopted'' (m + 1) * DriftStopped6.etaAdopted (m + 1)) := by linarith
  have hMu : GoodPathBounds.MAt (m + 1) (DriftStopped6c.c3Adopted'' (m + 1))
      ≤ 1 + 2 * (DriftStopped6.r0Adopted (m + 1)
        + DriftStopped6c.c3Adopted'' (m + 1) * DriftStopped6.etaAdopted (m + 1)) := by
    rw [hMAtEq]
    have hce : (0 : ℝ) ≤ DriftStopped6c.c3Adopted'' (m + 1) * DriftStopped6.etaAdopted (m + 1) :=
      by positivity
    linarith
  -- `δ = η/mAt`, in `1/q`
  have hdd0 := GoodPathBounds.deltaAt_nonneg hm1 hc3eta
  have hddq : GoodPathBounds.deltaAt (m + 1) (DriftStopped6c.c3Adopted'' (m + 1))
      ≤ 2 / Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ)) := by
    rw [GoodPathBounds.deltaAt, hmAtEq]
    exact delta_le_two_div hq0 hηq hmm
  have hq2 : (2 : ℝ) / Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ)) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ hq0 (by norm_num)]; linarith
  have hdd4 : GoodPathBounds.deltaAt (m + 1) (DriftStopped6c.c3Adopted'' (m + 1)) ≤ 1 / 4 := by
    linarith
  -- `rr = 2(1+c₃)η`, in `1/q`
  have hrr0 : (0 : ℝ) ≤ rrAt (m + 1) := by rw [rrAt]; positivity
  have hrrq : 2 * rrAt (m + 1) ≤ 12 / Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ)) := by
    rw [rrAt]
    exact rr_le_twelve hq0 hηq hc3q
  have hq12 : (12 : ℝ) / Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ)) ≤ 1 / 3 := by
    rw [div_le_div_iff₀ hq0 (by norm_num)]; linarith
  have hrrhalf : rrAt (m + 1) ≤ 1 / 2 := by linarith
  have hrm : (1 + DriftStopped6c.c3Adopted'' (m + 1)) * DriftStopped6.etaAdopted (m + 1)
      ≤ rrAt (m + 1) * (a0C (m + 1) - (DriftStopped6.r0Adopted (m + 1)
        + DriftStopped6c.c3Adopted'' (m + 1) * DriftStopped6.etaAdopted (m + 1))) := by
    rw [rrAt]
    have hnn : (0 : ℝ) ≤ (1 + DriftStopped6c.c3Adopted'' (m + 1))
        * DriftStopped6.etaAdopted (m + 1) := by positivity
    exact rm_ge hnn hmm
  -- `ε = 1/q`
  have heps0 : (0 : ℝ) < epsAt (m + 1) := by rw [epsAt]; positivity
  have hepsq : epsAt (m + 1) = 1 / Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ)) := rfl
  have hepsle : epsAt (m + 1) ≤ 1 := by
    rw [epsAt, div_le_one hq0]; linarith
  have hepsle5 : epsAt (m + 1) ≤ 1 / 5 := by
    rw [epsAt, div_le_div_iff₀ hq0 (by norm_num)]; linarith
  -- ### `κ` and `cqAt`
  have hkapup : (1 / 2 + 2 * rrAt (m + 1))
        / (a0C (m + 1) - (DriftStopped6.r0Adopted (m + 1)
          + DriftStopped6c.c3Adopted'' (m + 1) * DriftStopped6.etaAdopted (m + 1))) ^ 2
      ≤ 1 / 2 + 12 * (DriftStopped6.r0Adopted (m + 1)
          + DriftStopped6c.c3Adopted'' (m + 1) * DriftStopped6.etaAdopted (m + 1))
        + 2 * rrAt (m + 1) :=
    kappa_upper hmu hmm hmm1 hu0 hu3 hrr0 hrrhalf
  have hkaphalf : (1 : ℝ) / 2 ≤ (1 / 2 + 2 * rrAt (m + 1))
      / (a0C (m + 1) - (DriftStopped6.r0Adopted (m + 1)
        + DriftStopped6c.c3Adopted'' (m + 1) * DriftStopped6.etaAdopted (m + 1))) ^ 2 := by
    have h := AdoptedConstants95.kappa_ge_half (n := m + 1) (c₃ := DriftStopped6c.c3Adopted'' (m + 1))
      (rr := rrAt (m + 1)) hm1 hc30 hc3eta hrr0
    rwa [hmAtEq] at h
  have hkap5 : (1 / 2 + 2 * rrAt (m + 1))
      / (a0C (m + 1) - (DriftStopped6.r0Adopted (m + 1)
        + DriftStopped6c.c3Adopted'' (m + 1) * DriftStopped6.etaAdopted (m + 1))) ^ 2 ≤ 5 := by
    have hq120 : (12 : ℝ) * (10 / Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ))) ≤ 4 := by
      rw [show (12 : ℝ) * (10 / Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ)))
        = 120 / Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ)) by ring, div_le_iff₀ hq0]
      linarith
    have h12 : 12 * (DriftStopped6.r0Adopted (m + 1)
        + DriftStopped6c.c3Adopted'' (m + 1) * DriftStopped6.etaAdopted (m + 1)) ≤ 4 := by
      linarith
    linarith
  have hcqlow : 1 / 2 - 4 * (DriftStopped6.r0Adopted (m + 1)
        + DriftStopped6c.c3Adopted'' (m + 1) * DriftStopped6.etaAdopted (m + 1))
      - 3 * GoodPathBounds.deltaAt (m + 1) (DriftStopped6c.c3Adopted'' (m + 1))
      ≤ GoodPathBounds.cqAt (m + 1) (DriftStopped6c.c3Adopted'' (m + 1)) := by
    rw [GoodPathBounds.cqAt]
    exact cq_lower hMone hMu hu0 hu3 hdd0 hdd4
  -- ### positivity of the step scale
  have hηpos : (0 : ℝ) < DriftStopped6.etaAdopted (m + 1) := eta_pos hn3
  have hh0 : (0 : ℝ) < ParamsAdopted2.stepSizeAdopted2 (m + 1) :=
    TailSideSetup2.stepSizeAdopted2_pos hn3
  have hhne : ParamsAdopted2.stepSizeAdopted2 (m + 1) ≠ 0 := ne_of_gt hh0
  have hcsq := TruncSumMean.cAdopted_sq (n := m + 1) hn3
  have hfr : (finrank ℝ (EuclideanSpace ℝ (UT (m + 1))) : ℝ)
      = (Fintype.card (UT (m + 1)) : ℝ) := by rw [finrank_euclideanSpace]
  have hlt := GoodPathBounds.lt_a0C_of_mAt hm1 hc3eta
  have hlog1 : (1 : ℝ) ≤ Real.log ((m + 1 : ℕ) : ℝ) := ChainDrift.log_pos_of_three hn3
  have hlog4 := WindowR.log_le_four_qrt hm1
  -- ### the primes
  have hp1 : 1 < p := Nat.Prime.one_lt (Fact.out : Nat.Prime p)
  have hp1R : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp1.le
  have hpn1 : (1 : ℝ) ≤ ((p ^ (m + 1 - 1) : ℕ) : ℝ) := by
    have : 1 ≤ p ^ (m + 1 - 1) := Nat.one_le_pow _ _ (by omega)
    exact_mod_cast this
  have hppos1 : (1 : ℝ) < (p : ℝ) ^ (m + 1) :=
    one_lt_pow₀ (by exact_mod_cast hp1) (by omega)
  -- ### the two thresholds
  have hthetaB : ThetaTight.thetaTight p (m + 1)
      (TailAtStepR5W2.C3 (m + 1) 1 (Bfam m) α) ≤ 2800000 := by
    have hBm : Bfam m = 140 / ((m + 1 : ℕ) : ℝ) ^ 2 := rfl
    rw [hBm]
    exact thetaTight_le_2800000 hm1 hα hraw.tiling_defect hraw.alpha_norm hp1R hpn1 hppos1
  have hThT0 : (0 : ℝ) < 10000 * ((m + 1 : ℕ) : ℝ) ^ 2 := by positivity
  have hBmul : Bfam m * (2 * (10000 * ((m + 1 : ℕ) : ℝ) ^ 2)) = 2800000 := by
    rw [Bfam]; field_simp; ring
  have h₁ : Theorem2R4.θ3 1 (Bfam m) p m α
      ≤ ENNReal.ofReal 1 * ENNReal.ofReal 2800000 := by
    rw [Theorem2R4.θ3, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1), one_mul]
    exact ENNReal.ofReal_le_ofReal hthetaB
  have h₂ : Theorem2R4.θ3 1 (Bfam m) p m α
      ≤ ENNReal.ofReal (Bfam m) * ENNReal.ofReal (2 * (10000 * ((m + 1 : ℕ) : ℝ) ^ 2)) := by
    rw [Theorem2R4.θ3, ← ENNReal.ofReal_mul (Bfam_nonneg m), hBmul]
    exact ENNReal.ofReal_le_ofReal hthetaB
  -- ### the count
  have hcnt := TailWiring.hcnt_win (p := p) (m := m) (α := α) (A := 1) (B := Bfam m)
    (Θ := 2800000) (ΘT := 10000 * ((m + 1 : ℕ) : ℝ) ^ 2)
    (c₃ := DriftStopped6c.c3Adopted'' (m + 1)) (K := Kcut m)
    hm hα one_pos (Bfam_nonneg m) g hraw hnd hKlt hc3pos (by norm_num) hThT0 h₁ h₂ hlight
  have hpcnt0 : (0 : ℝ) ≤ (2 * (10000 * ((m + 1 : ℕ) : ℝ) ^ 2) + 0)
      / DriftStopped6c.c3Adopted'' (m + 1) := by positivity
  have hpcq : (2 * (10000 * ((m + 1 : ℕ) : ℝ) ^ 2) + 0) / DriftStopped6c.c3Adopted'' (m + 1)
      ≤ 2 * 10000 / Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ)) ^ 3 :=
    count_ratio_q hm1 (by norm_num) (le_refl _)
  -- ### the failure total
  have hlog0 : (0 : ℝ) ≤ Real.log ((m + 1 : ℕ) : ℝ) := by linarith
  have hpbad0 : (0 : ℝ) ≤ GoodPathBounds.failTotal (m + 1)
      ((2 * (10000 * ((m + 1 : ℕ) : ℝ) ^ 2) + 0) / DriftStopped6c.c3Adopted'' (m + 1)) :=
    failTotal_nonneg hn3 hpcnt0
  have hfi := failTotal_le_inv hm1
    ((2 * (10000 * ((m + 1 : ℕ) : ℝ) ^ 2) + 0) / DriftStopped6c.c3Adopted'' (m + 1))
  -- ### the goodCut failure, and `hS`
  have hξm : ∀ j, Measurable
      (ChainSetup.step (ι := UT (m + 1)) (Submission.L10.cAdopted (m + 1)) j) :=
    fun j => ChainSetup.measurable_step _ j
  have hGms : ∀ k, MeasurableSet[ChainSetup.filtration
        (F := EuclideanSpace ℝ (UT (m + 1))) k]
      (stateGood (qC α) (windowOfR2 α p m g) (A0C (m + 1))
        (ChainSetup.step (Submission.L10.cAdopted (m + 1)))
        (DriftStopped6.etaAdopted (m + 1)) (DriftStopped6.r0Adopted (m + 1))
        (DriftStopped6c.c3Adopted'' (m + 1)) k) :=
    fun k => DriftInputsStopped.measurableSet_stateGood_step _ _ _ _ k
  have hτ : Measurable (tau (qC α) (windowOfR2 α p m g) (A0C (m + 1))
      (ChainSetup.step (Submission.L10.cAdopted (m + 1)))
      (DriftStopped6.etaAdopted (m + 1)) (DriftStopped6.r0Adopted (m + 1))
      (DriftStopped6c.c3Adopted'' (m + 1)) (ParamsAdopted2.numStepsAdopted2 (m + 1))) :=
    DriftStopped5.measurable_tau
      (ChainSetup.filtration (F := EuclideanSpace ℝ (UT (m + 1)))) hGms _
  have hfail : (ChainSetup.gaussPath (EuclideanSpace ℝ (UT (m + 1)))).real
      (GoodPathBounds.goodCut 1 (ChainSetup.coord 0)
        (ChainSetup.step (Submission.L10.cAdopted (m + 1)))
        (6 * 1 * 1 * Real.sqrt ((m + 1 : ℕ) : ℝ))
        (ParamsAdopted2.numStepsAdopted2 (m + 1)) (DriftStopped6.etaAdopted (m + 1))
        (qC α) (windowOfR2 α p m g) (A0C (m + 1)) (DriftStopped6.r0Adopted (m + 1))
        (DriftStopped6c.c3Adopted'' (m + 1)) (Kcut m))ᶜ
      ≤ GoodPathBounds.failTotal (m + 1)
        ((2 * (10000 * ((m + 1 : ℕ) : ℝ) ^ 2) + 0)
          / DriftStopped6c.c3Adopted'' (m + 1)) :=
    goodCut_fail_le hn3 hcnt
  have hSlight := TailWiring.hS_light_win (p := p) (m := m) (α := α) (A := 1) (B := Bfam m)
    (Θ := 2800000) (ΘT := 10000 * ((m + 1 : ℕ) : ℝ) ^ 2) (K := Kcut m)
    hm hα one_pos (Bfam_nonneg m) g hraw hnd hKleN (by norm_num) hThT0 h₁ h₂ hlight
  -- ### the remaining size bounds
  have hkap0 : (0 : ℝ) ≤ ((1 / 2 + 2 * rrAt (m + 1)) / (a0C (m + 1) - ((DriftStopped6.r0Adopted (m + 1)) + (DriftStopped6c.c3Adopted'' (m + 1)) * (DriftStopped6.etaAdopted (m + 1)))) ^ 2) := by linarith
  have hEa : (DriftAccumulated.EaccAt (m + 1) (DriftStopped6c.c3Adopted'' (m + 1))) ≤ 1 := by
    rw [DriftAccumulated.EaccAt_eq]
    have hid : (DriftStopped6c.c3Adopted'' (m + 1)) * ((DriftStopped6.etaAdopted (m + 1)) / GoodPathBounds.mAt (m + 1) (DriftStopped6c.c3Adopted'' (m + 1)))
        = ((DriftStopped6c.c3Adopted'' (m + 1)) * (DriftStopped6.etaAdopted (m + 1))) / GoodPathBounds.mAt (m + 1) (DriftStopped6c.c3Adopted'' (m + 1)) := by ring
    rw [hid, div_le_one (by linarith)]
    linarith
  have hCB := DriftStopped6b.slackHyp_at hm1 hc30 hc3eta
  rw [DriftStopped4.SlackHyp, DriftStopped6.slackAdopted] at hCB
  have hce0 : (0 : ℝ) ≤ (DriftStopped6c.c3Adopted'' (m + 1)) * (DriftStopped6.etaAdopted (m + 1)) := by positivity
  have hsq2 : (2 / (Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ)))) ^ 2 = 4 / (Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ))) ^ 2 := by rw [div_pow]; norm_num
  have hxx : ((DriftStopped6c.c3Adopted'' (m + 1)) * (DriftStopped6.etaAdopted (m + 1))) ^ 2 ≤ 4 / (Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ))) ^ 2 :=
    hsq2 ▸ pow_le_pow_left₀ hce0 hc3q 2
  have hGle : ((Kcut m : ℝ) * (Submission.L10.cAdopted (m + 1) ^ 2 * ((finrank ℝ (EuclideanSpace ℝ (UT (m + 1))) : ℝ)))) ≤ 64 * (Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ))) := by
    have hassoc : ((Kcut m : ℝ) * (Submission.L10.cAdopted (m + 1) ^ 2 * ((finrank ℝ (EuclideanSpace ℝ (UT (m + 1))) : ℝ))))
        = ((Kcut m : ℝ) * ParamsAdopted2.stepSizeAdopted2 (m + 1))
          * (Fintype.card (UT (m + 1)) : ℝ) := by rw [hcsq, hfr]; ring
    have hNh := ParamsAdopted2.numStepsAdopted2_mul_stepSizeAdopted2 hn3
    have hKh : (Kcut m : ℝ) * ParamsAdopted2.stepSizeAdopted2 (m + 1)
        ≤ ChainDrift.horizon (m + 1) := by
      rw [← hNh]; exact mul_le_mul_of_nonneg_right hKle hh0.le
    have hcard0 : (0 : ℝ) ≤ (Fintype.card (UT (m + 1)) : ℝ) := Nat.cast_nonneg _
    have hstep := mul_le_mul_of_nonneg_right hKh hcard0
    have hhc := horizon_mul_card_le (n := m + 1) hm1
    rw [hassoc]
    linarith
  have hG0 : (0 : ℝ) ≤ ((Kcut m : ℝ) * (Submission.L10.cAdopted (m + 1) ^ 2 * ((finrank ℝ (EuclideanSpace ℝ (UT (m + 1))) : ℝ)))) := by positivity
  -- `q·pbad ≤ 16`
  have hqpc := mul_le_mul_of_nonneg_left hpcq hq0.le
  have hid1 : (Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ))) * (2 * 10000 / (Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ))) ^ 3) = 20000 / (Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ))) ^ 2 := by
    field_simp; ring
  have hq2b : (20000 : ℝ) / (Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ))) ^ 2 ≤ 15 :=
    twenty_k_div_sq_le hq37
  have hqfi := mul_le_mul_of_nonneg_left hfi hq0.le
  have hid2 : (Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ))) * (((2 * (10000 * ((m + 1 : ℕ) : ℝ) ^ 2) + 0) / (DriftStopped6c.c3Adopted'' (m + 1))) + 1 / (1000 * ((m + 1 : ℕ) : ℝ)))
      = (Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ))) * ((2 * (10000 * ((m + 1 : ℕ) : ℝ) ^ 2) + 0) / (DriftStopped6c.c3Adopted'' (m + 1))) + (Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ))) * (1 / (1000 * ((m + 1 : ℕ) : ℝ))) := by ring
  have hqn : (Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ))) * (1 / (1000 * ((m + 1 : ℕ) : ℝ))) ≤ 1 / 1000 := by
    rw [show (Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ))) * (1 / (1000 * ((m + 1 : ℕ) : ℝ)))
      = (Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ))) / (1000 * ((m + 1 : ℕ) : ℝ)) by ring,
      div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith [hqle]
  have hpb : (Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ))) * (GoodPathBounds.failTotal (m + 1) ((2 * (10000 * ((m + 1 : ℕ) : ℝ) ^ 2) + 0) / (DriftStopped6c.c3Adopted'' (m + 1)))) ≤ 16 := by
    linarith [hqfi, hid2.le, hid2.ge, hqpc, hid1.le, hid1.ge, hq2b, hqn]
  -- the gap `κ(1+ε) − cqAt ≤ 200/q`
  have hgap : ((1 / 2 + 2 * rrAt (m + 1)) / (a0C (m + 1) - ((DriftStopped6.r0Adopted (m + 1)) + (DriftStopped6c.c3Adopted'' (m + 1)) * (DriftStopped6.etaAdopted (m + 1)))) ^ 2) * (1 + epsAt (m + 1)) - (GoodPathBounds.cqAt (m + 1) (DriftStopped6c.c3Adopted'' (m + 1))) ≤ 200 / (Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ))) := by
    have hinvid : ∀ c : ℝ, c / (Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ))) = c * (1 / (Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ)))) := fun c => by ring
    have hkeps := mul_le_mul_of_nonneg_right hkap5 heps0.le
    rw [hepsq] at hkeps
    rw [hepsq, hinvid 200]
    rw [hinvid 10] at huq
    rw [hinvid 12] at hrrq
    rw [hinvid 2] at hddq
    exact gap_le (by positivity) hkapup hcqlow huq hrrq hddq hkeps
  -- ### the five conjuncts
  refine ⟨((Kcut m : ℝ) * ((finrank ℝ (EuclideanSpace ℝ (UT (m + 1))) : ℝ))
      - 2800000 / ParamsAdopted2.stepSizeAdopted2 (m + 1)
      - ((finrank ℝ (EuclideanSpace ℝ (UT (m + 1))) : ℝ)) * ((Kcut m : ℝ) * GoodPathBounds.failTotal (m + 1) ((2 * (10000 * ((m + 1 : ℕ) : ℝ) ^ 2) + 0) / (DriftStopped6c.c3Adopted'' (m + 1))))), ((2 * (10000 * ((m + 1 : ℕ) : ℝ) ^ 2) + 0) / (DriftStopped6c.c3Adopted'' (m + 1))), (ChainWiring.logDet (A0C (m + 1)) - ((DriftChargeTotal.driftCen (n := m + 1) (Submission.L10.cAdopted (m + 1))
          (DriftStopped6.etaAdopted (m + 1)) (DriftStopped6c.c3Adopted'' (m + 1)) ((1 / 2 + 2 * rrAt (m + 1)) / (a0C (m + 1) - ((DriftStopped6.r0Adopted (m + 1)) + (DriftStopped6c.c3Adopted'' (m + 1)) * (DriftStopped6.etaAdopted (m + 1)))) ^ 2) (epsAt (m + 1)) (Kcut m)) + 1) - 1), 20, ?_, ?_, ?_, ?_, ?_⟩
  · exact hS_of_intWeight_cut hh0 hKlt hξm hτ hSlight hfail
  · exact hcnt
  · refine le_trans (ChainShortfall.hshort_at_chain (n := m + 1) (xs := xOf α)
      (W := windowOfR2 α p m g) (A₀ := A0C (m + 1)) (η := (DriftStopped6.etaAdopted (m + 1)))
      (a₀ := a0C (m + 1)) (r₀ := (DriftStopped6.r0Adopted (m + 1))) (c₃ := (DriftStopped6c.c3Adopted'' (m + 1)))
      (rr := rrAt (m + 1)) (ε := epsAt (m + 1)) (cstep := Submission.L10.cAdopted (m + 1))
      (t := 1) (t' := 1) (s' := 1) (N := ParamsAdopted2.numStepsAdopted2 (m + 1))
      (K := Kcut m)
      hN1 hξm hτ (kSet_A0C_win hα hn3) (hq_win hα hn3) (hne_win hα hn3)
      (StateSupply.symMat_A0C (m + 1)) hη0 hr00 hc30 hlt hrr0 hrrhalf hrm heps0
      (by norm_num) (by norm_num) (by norm_num)) ?_
    refine shortfall_le_twenty ?_ (vterm_le hm1 hKle hmm) ?_ (wterm_le hm1 hKle) ?_ ?_
    · positivity
    · positivity
    · have h1 : (0 : ℝ) ≤ 1 + epsAt (m + 1) := by linarith
      exact mul_nonneg hkap0 h1
    · exact kp_le_six hkap0 hkap5 heps0.le hepsle5
  · exact hLb_of_bounds_cut hm1 hkaphalf hkap0 heps0 (by norm_num) (by norm_num) hKsucc
      (by norm_num)
  · have hcenle := driftCen_le (n := m + 1) hn3 (c := Submission.L10.cAdopted (m + 1))
      (κ := ((1 / 2 + 2 * rrAt (m + 1)) / (a0C (m + 1) - ((DriftStopped6.r0Adopted (m + 1)) + (DriftStopped6c.c3Adopted'' (m + 1)) * (DriftStopped6.etaAdopted (m + 1)))) ^ 2)) (ε := epsAt (m + 1)) (c₃ := (DriftStopped6c.c3Adopted'' (m + 1))) (η := (DriftStopped6.etaAdopted (m + 1)))
      hηpos hkap0 heps0 (Kcut m)
    have hnum := num_le_const (qv := (Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ)))) hq37 hepsq hcenle hgap hG0 hGle hkap0 hkap5
      (by positivity) hxx hcq0 hcqh (by norm_num) (le_refl (2800000 : ℝ)) hpbad0 hpb
      hEa hCB (le_refl (1 : ℝ)) (le_refl (1 : ℝ)) (le_refl (20 : ℝ))
    refine budget_lt_one'' (Anum := 1450000) (Bden := 9999000) (Fb := 2 / 5)
      (by norm_num) (by norm_num) ?_ ?_ ?_ (by norm_num)
    · have hid : DriftAccumulated.driftRHS_acc (m + 1) (A0C (m + 1)) (DriftStopped6c.c3Adopted'' (m + 1)) (DriftAccumulated.EaccAt (m + 1) (DriftStopped6c.c3Adopted'' (m + 1))) ((Kcut m : ℝ) * ((finrank ℝ (EuclideanSpace ℝ (UT (m + 1))) : ℝ))
      - 2800000 / ParamsAdopted2.stepSizeAdopted2 (m + 1)
      - ((finrank ℝ (EuclideanSpace ℝ (UT (m + 1))) : ℝ)) * ((Kcut m : ℝ) * GoodPathBounds.failTotal (m + 1) ((2 * (10000 * ((m + 1 : ℕ) : ℝ) ^ 2) + 0) / (DriftStopped6c.c3Adopted'' (m + 1)))))
            - (ChainWiring.logDet (A0C (m + 1)) - ((DriftChargeTotal.driftCen (n := m + 1) (Submission.L10.cAdopted (m + 1))
          (DriftStopped6.etaAdopted (m + 1)) (DriftStopped6c.c3Adopted'' (m + 1)) ((1 / 2 + 2 * rrAt (m + 1)) / (a0C (m + 1) - ((DriftStopped6.r0Adopted (m + 1)) + (DriftStopped6c.c3Adopted'' (m + 1)) * (DriftStopped6.etaAdopted (m + 1)))) ^ 2) (epsAt (m + 1)) (Kcut m)) + 1) - 1) + 20
          = (DriftChargeTotal.driftCen (n := m + 1) (Submission.L10.cAdopted (m + 1))
          (DriftStopped6.etaAdopted (m + 1)) (DriftStopped6c.c3Adopted'' (m + 1)) ((1 / 2 + 2 * rrAt (m + 1)) / (a0C (m + 1) - ((DriftStopped6.r0Adopted (m + 1)) + (DriftStopped6c.c3Adopted'' (m + 1)) * (DriftStopped6.etaAdopted (m + 1)))) ^ 2) (epsAt (m + 1)) (Kcut m)) - (GoodPathBounds.cqAt (m + 1) (DriftStopped6c.c3Adopted'' (m + 1))) * ((Kcut m : ℝ) * (Submission.L10.cAdopted (m + 1) ^ 2 * ((finrank ℝ (EuclideanSpace ℝ (UT (m + 1))) : ℝ)))) + (GoodPathBounds.cqAt (m + 1) (DriftStopped6c.c3Adopted'' (m + 1))) * 2800000 + (GoodPathBounds.cqAt (m + 1) (DriftStopped6c.c3Adopted'' (m + 1))) * ((Kcut m : ℝ) * (Submission.L10.cAdopted (m + 1) ^ 2 * ((finrank ℝ (EuclideanSpace ℝ (UT (m + 1))) : ℝ)))) * (GoodPathBounds.failTotal (m + 1) ((2 * (10000 * ((m + 1 : ℕ) : ℝ) ^ 2) + 0) / (DriftStopped6c.c3Adopted'' (m + 1))))
            + (DriftAccumulated.EaccAt (m + 1) (DriftStopped6c.c3Adopted'' (m + 1))) + (DriftStopped4.C₁ (m + 1) (GoodPathBounds.mAt (m + 1) (DriftStopped6c.c3Adopted'' (m + 1))) (GoodPathBounds.cqAt (m + 1) (DriftStopped6c.c3Adopted'' (m + 1)))
            * (2 * Submission.L10.B_adopted (m + 1))) + 1 + 1 + 20 := by
        rw [DriftAccumulated.driftRHS_acc, hcsq]
        exact rhs_identity hhne
      rw [hid]
      exact hnum
    · have hcenge := driftCen_ge_cut (n := m + 1) (c₃ := (DriftStopped6c.c3Adopted'' (m + 1))) hm1 hkaphalf hkap0 heps0 hKsucc
      have hA0 := AdoptedConstants95.logDet_A0C_le (n := m + 1) hn3
      have hsmall := log_div_le (n := m + 1) hm1
      linarith
    · have hpc3b : 2 * 10000 / (Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ))) ^ 3 ≤ 396 / 1000 :=
        twenty_k_div_cube_le hq37
      have hinvn : 1 / (1000 * ((m + 1 : ℕ) : ℝ)) ≤ 1 / 1000 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
      linarith [hfi, hpcq, hpc3b, hinvn]

end Submission.L10.FinalTheorem

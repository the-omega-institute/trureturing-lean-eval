import Submission.L10.DriftStopped6
import Submission.L10.GaussianMaximal3
import Submission.L10.Theorem3

/-!
# Gate L-10 (`klartag_packing`) — the drift side's numeric obligation, and the window it runs on

Brief 62, second pass, after four route notes.  `DriftStopped6.lean` is reported and is not edited
(rule 5); this module imports it.

Three things changed under the drift side while brief 62 was running, and all three are now
theorems in the tree rather than hypotheses:

* `Theorem2.lean`/`Theorem3.lean` (brief 65) keep the **light-contact** fact
  `Section5.exists_good_line_of_chainData` proves and `Assembly.exists_phi_of_params` discarded, so
  the drift side is handed it.  `Theorem3.DriftSide''` (`:36`) is the gate's single remaining hole.
* `GaussianMaximal3.lean` (brief 63) discharges `MaximalAtAdopted` and `IntegrableAtIndex` at the
  adopted scale with no hypothesis beyond `3 ≤ n`.
* `LatticeData.lean` (brief 64) restricts `RawData`, `NormData` and `TailSideHyp` to a sub-window.

## What is here

1. **`slackHyp_adopted`** — the numeric obligation, proved for **every** `n ≥ 2 073 600` with no
   other hypothesis.  It is the last conjunct of `DriftStopped4.Brief54Obligation` that was not
   already a theorem, so `brief54Obligation_adopted` now closes the whole obligation outright.
   The chain of bounds, each in §1: `log n ≤ 4·n^{1/4}` gives `r₀ ≤ 1/4`; `η ≤ √2·n⁻³` gives
   `c₃η ≤ √2/n ≤ 1/4`; `a₀ ≥ 1` then gives `m ≥ 1/2` and `M ≥ 1`, hence `c ≤ 1/2` and
   `C₁ = c + √n/m ≤ 3√n`; `GaussianMaximal3.B_adopted_le` gives `B ≤ 5/n³`; so
   `C₁·2B ≤ 30√n/n³ ≤ 1`.  (Numerically `3.2·10⁻¹⁸` at the threshold — report 62 §4.)
2. **`windowOf`** — the window the drift side actually runs the chain on, `W_g = W.filter (· ∈
   latZ p n g)`, with the restriction of all three data structures to it.
3. **`DriftResidual`** and **`driftSide''_of_residual`** — `Theorem3.DriftSide''` reduced: the
   residual is handed the sub-window data, the whole maximal obligation and the integrability, and
   owes only `Assembly.ChainOutput`.  `klartag_packing_of_residual` composes it with
   `Theorem3.klartag_packing_of_drift` to the challenge statement.

## What is still missing

The same theorem report 62 §3 named, now in its final shape: from a path of
`StateInvariant4.wiredGood'` on `W_g` whose terminal log-determinant obeys eq. (68), build the
ellipsoid and the lattice avoidance.  It is lattice geometry, not probability.
-/

set_option linter.unusedSectionVars false

namespace Submission.L10.DriftStopped7

open MeasureTheory Matrix Finset Module Submission.L10 Submission.L10.Increments
open Submission.L10.DriftStopped4 Submission.L10.DriftStopped5
open Submission.L10.ConstructionA Submission.L10.Tiling Submission.L10.PaddedLawSetup
open Submission.L10.TailSideSetup2 Submission.L10.RawDataInst2 Submission.L10.Section5
open scoped ENNReal RealInnerProductSpace

/-! ## 1. The numeric obligation -/

section Numeric

variable {n : ℕ}



theorem log_le_four_sqrt_sqrt (hn : 1 ≤ n) :
    Real.log n ≤ 4 * Real.sqrt (Real.sqrt (n : ℝ)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hs0 : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
  have ht0 : (0 : ℝ) < Real.sqrt (Real.sqrt (n : ℝ)) := Real.sqrt_pos.2 hs0
  have h1 : Real.log (Real.sqrt (Real.sqrt (n : ℝ))) ≤ Real.sqrt (Real.sqrt (n : ℝ)) - 1 :=
    Real.log_le_sub_one_of_pos ht0
  have h2 : Real.log (Real.sqrt (n : ℝ)) = Real.log n / 2 := Real.log_sqrt hn0.le
  have h3 : Real.log (Real.sqrt (Real.sqrt (n : ℝ))) = Real.log (Real.sqrt (n : ℝ)) / 2 :=
    Real.log_sqrt (Real.sqrt_nonneg _)
  linarith

theorem sqrt_ge_1440 (hn : 2073600 ≤ n) : (1440 : ℝ) ≤ Real.sqrt (n : ℝ) := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [show (1440 : ℝ) = Real.sqrt (1440 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt (by norm_num; linarith)

theorem sqrt_sqrt_ge (hn : 2073600 ≤ n) : (37 : ℝ) ≤ Real.sqrt (Real.sqrt (n : ℝ)) := by
  have hs := sqrt_ge_1440 hn
  rw [show (37 : ℝ) = Real.sqrt (37 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt (by linarith)

theorem log_div_le (hn : 2073600 ≤ n) : Real.log n / (n : ℝ) ≤ (1 / 96 : ℝ) ^ 2 := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  set t := Real.sqrt (Real.sqrt (n : ℝ)) with ht
  have ht37 : (37 : ℝ) ≤ t := sqrt_sqrt_ge hn
  have ht0 : (0 : ℝ) < t := by linarith
  have hsq : t ^ 2 = Real.sqrt (n : ℝ) := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hn4 : t ^ 4 = (n : ℝ) := by
    have h : (t ^ 2) ^ 2 = (n : ℝ) := by rw [hsq]; exact Real.sq_sqrt hn0.le
    nlinarith [h]
  have hlog : Real.log n ≤ 4 * t := log_le_four_sqrt_sqrt (by omega)
  rw [div_le_iff₀ hn0]
  have hkey : 4 * t ≤ (1 / 96 : ℝ) ^ 2 * (n : ℝ) := by
    rw [← hn4]
    nlinarith [ht37, ht0, pow_pos ht0 3]
  linarith

/-! ## The adopted constants, bounded -/

theorem r0Adopted_nonneg : 0 ≤ DriftStopped6.r0Adopted n := by
  rw [DriftStopped6.r0Adopted]; positivity

theorem etaAdopted_nonneg : 0 ≤ DriftStopped6.etaAdopted n := by
  rw [DriftStopped6.etaAdopted]; exact Real.sqrt_nonneg _

theorem r0Adopted_le (hn : 2073600 ≤ n) : DriftStopped6.r0Adopted n ≤ 1 / 4 := by
  have h := log_div_le hn
  have hs : Real.sqrt (Real.log n / (n : ℝ)) ≤ 1 / 96 := by
    rw [show (1 : ℝ) / 96 = Real.sqrt ((1 / 96) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt h
  rw [DriftStopped6.r0Adopted]
  linarith

theorem c3_mul_eta_le (hn : 2073600 ≤ n) :
    DriftStopped6.c3Adopted n * DriftStopped6.etaAdopted n ≤ 1 / 4 := by
  have hn3 : 3 ≤ n := by omega
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have heta : DriftStopped6.etaAdopted n ≤ Real.sqrt 2 / (n : ℝ) ^ 3 :=
    ParamsAdopted2.eta2_le hn3
  have h2 : Real.sqrt 2 ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt (2 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hstep : DriftStopped6.c3Adopted n * DriftStopped6.etaAdopted n
      ≤ (n : ℝ) ^ 2 * (Real.sqrt 2 / (n : ℝ) ^ 3) := by
    rw [DriftStopped6.c3Adopted]
    exact mul_le_mul_of_nonneg_left heta (by positivity)
  have hval : (n : ℝ) ^ 2 * (Real.sqrt 2 / (n : ℝ) ^ 3) = Real.sqrt 2 / (n : ℝ) := by
    field_simp
  rw [hval] at hstep
  have hfin : Real.sqrt 2 / (n : ℝ) ≤ 2 / (2073600 : ℝ) := by
    rw [div_le_div_iff₀ hn0 (by norm_num)]
    nlinarith [h2, hnR, Real.sqrt_nonneg (2 : ℝ)]
  linarith

theorem one_le_a0C (hn : 2 ≤ n) : (1 : ℝ) ≤ a0C n := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hinv : 1 / (n : ℝ) ≤ 1 / 2 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR
  have hpos : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  have h1 : (0 : ℝ) < 1 - 1 / (n : ℝ) := by linarith
  have h2 : 1 - 1 / (n : ℝ) ≤ 1 := by linarith
  have hmul : (1 - 1 / (n : ℝ))⁻¹ * (1 - 1 / (n : ℝ)) = 1 := inv_mul_cancel₀ (ne_of_gt h1)
  have hxi : (0 : ℝ) < (1 - 1 / (n : ℝ))⁻¹ := inv_pos.2 h1
  have h3 : (1 : ℝ) ≤ (1 - 1 / (n : ℝ))⁻¹ := by nlinarith [hmul, hxi, h2]
  rw [a0C]
  nlinarith [h3]

theorem half_le_mAdopted (hn : 2073600 ≤ n) : (1 : ℝ) / 2 ≤ DriftStopped6.mAdopted n := by
  have h1 := one_le_a0C (n := n) (by omega)
  have h2 := r0Adopted_le hn
  have h3 := c3_mul_eta_le hn
  rw [DriftStopped6.mAdopted]
  linarith

theorem one_le_MAdopted (hn : 2073600 ≤ n) : (1 : ℝ) ≤ DriftStopped6.MAdopted n := by
  have h1 := one_le_a0C (n := n) (by omega)
  have h2 : 0 ≤ DriftStopped6.r0Adopted n := r0Adopted_nonneg
  have h3 : 0 ≤ DriftStopped6.c3Adopted n * DriftStopped6.etaAdopted n := by
    rw [DriftStopped6.c3Adopted]
    exact mul_nonneg (by positivity) etaAdopted_nonneg
  rw [DriftStopped6.MAdopted]
  linarith

theorem deltaAdopted_nonneg (hn : 2073600 ≤ n) : 0 ≤ DriftStopped6.deltaAdopted n := by
  have hm := half_le_mAdopted hn
  rw [DriftStopped6.deltaAdopted]
  exact div_nonneg etaAdopted_nonneg (by linarith)

theorem two_le_cAdopted_den (hn : 2073600 ≤ n) :
    (2 : ℝ) ≤ 2 * DriftStopped6.MAdopted n ^ 2 * (1 + DriftStopped6.deltaAdopted n) ^ 2 := by
  have hM := one_le_MAdopted hn
  have hd := deltaAdopted_nonneg hn
  have hM2 : (1 : ℝ) ≤ DriftStopped6.MAdopted n ^ 2 := by nlinarith
  have hd2 : (1 : ℝ) ≤ (1 + DriftStopped6.deltaAdopted n) ^ 2 := by nlinarith
  have hprod : (1 : ℝ) * 1
      ≤ DriftStopped6.MAdopted n ^ 2 * (1 + DriftStopped6.deltaAdopted n) ^ 2 :=
    mul_le_mul hM2 hd2 (by norm_num) (by positivity)
  linarith

theorem cAdopted_nonneg (hn : 2073600 ≤ n) : 0 ≤ DriftStopped6.cAdopted n := by
  have h := two_le_cAdopted_den hn
  rw [DriftStopped6.cAdopted]
  exact div_nonneg zero_le_one (by linarith)

theorem cAdopted_le_half (hn : 2073600 ≤ n) : DriftStopped6.cAdopted n ≤ 1 / 2 := by
  have h := two_le_cAdopted_den hn
  rw [DriftStopped6.cAdopted]
  exact one_div_le_one_div_of_le (by norm_num) h

theorem C₁_le (hn : 2073600 ≤ n) :
    C₁ n (DriftStopped6.mAdopted n) (DriftStopped6.cAdopted n) ≤ 3 * Real.sqrt (n : ℝ) := by
  have hm := half_le_mAdopted hn
  have hc := cAdopted_le_half hn
  have hs := sqrt_ge_1440 hn
  have hdiv : Real.sqrt (n : ℝ) / DriftStopped6.mAdopted n ≤ 2 * Real.sqrt (n : ℝ) := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [Real.sqrt_nonneg ((n : ℝ)), hm, hs]
  rw [C₁]
  linarith

/-! ## `B_adopted`, bounded by `5/n³` -/

theorem sqrt_hd_le (hn : 2073600 ≤ n) :
    Real.sqrt (ParamsAdopted2.stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ))
      ≤ 1 / ((n : ℝ) ^ 3 * Real.sqrt (n : ℝ)) := by
  have hn3 : 3 ≤ n := by omega
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
  have hd : (Fintype.card (UT n) : ℝ) ≤ (n : ℝ) ^ 2 := Discharge.card_UT_le_sq (by omega)
  have hh : ParamsAdopted2.stepSizeAdopted2 n ≤ 1 / (n : ℝ) ^ 9 :=
    ParamsAdopted2.stepSizeAdopted2_le hn3
  have hh0 : 0 ≤ ParamsAdopted2.stepSizeAdopted2 n := ParamsAdopted2.stepSizeAdopted2_nonneg hn3
  have hprod : ParamsAdopted2.stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ)
      ≤ 1 / (n : ℝ) ^ 7 := by
    have h1 : ParamsAdopted2.stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ)
        ≤ (1 / (n : ℝ) ^ 9) * (n : ℝ) ^ 2 :=
      mul_le_mul hh hd (Nat.cast_nonneg _) (by positivity)
    have h2 : (1 / (n : ℝ) ^ 9) * (n : ℝ) ^ 2 = 1 / (n : ℝ) ^ 7 := by field_simp
    linarith
  have hrepr : (1 : ℝ) / (n : ℝ) ^ 7 = (1 / ((n : ℝ) ^ 3 * Real.sqrt (n : ℝ))) ^ 2 := by
    have hsq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hn0.le
    field_simp
    nlinarith [hsq, hn0]
  calc Real.sqrt (ParamsAdopted2.stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ))
      ≤ Real.sqrt ((1 / ((n : ℝ) ^ 3 * Real.sqrt (n : ℝ))) ^ 2) := by
        rw [← hrepr]; exact Real.sqrt_le_sqrt hprod
    _ = 1 / ((n : ℝ) ^ 3 * Real.sqrt (n : ℝ)) := Real.sqrt_sq (by positivity)

theorem B_adopted_le' (hn : 2073600 ≤ n) : B_adopted n ≤ 5 / (n : ℝ) ^ 3 := by
  have hn3 : 3 ≤ n := by omega
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
  have hlogn : Real.log n ≤ (n : ℝ) := by
    have := Real.log_le_sub_one_of_pos hn0
    linarith
  have hsl : Real.sqrt (Real.log n) ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt hlogn
  have hhd := sqrt_hd_le hn
  have hhd0 : 0 ≤ Real.sqrt (ParamsAdopted2.stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ)) :=
    Real.sqrt_nonneg _
  have hmain : 5 * Real.sqrt (ParamsAdopted2.stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ))
      * Real.sqrt (Real.log n) ≤ 5 / (n : ℝ) ^ 3 := by
    have h1 : 5 * Real.sqrt (ParamsAdopted2.stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ))
        * Real.sqrt (Real.log n)
        ≤ 5 * (1 / ((n : ℝ) ^ 3 * Real.sqrt (n : ℝ))) * Real.sqrt (n : ℝ) := by
      have hA : Real.sqrt (ParamsAdopted2.stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ))
          * Real.sqrt (Real.log n)
          ≤ (1 / ((n : ℝ) ^ 3 * Real.sqrt (n : ℝ))) * Real.sqrt (n : ℝ) :=
        mul_le_mul hhd hsl (Real.sqrt_nonneg _) (by positivity)
      linarith
    have h2 : 5 * (1 / ((n : ℝ) ^ 3 * Real.sqrt (n : ℝ))) * Real.sqrt (n : ℝ)
        = 5 / (n : ℝ) ^ 3 := by field_simp
    linarith
  exact le_trans (B_adopted_le hn) hmain

theorem B_adopted_nonneg (hn : 2073600 ≤ n) : 0 ≤ B_adopted n := by
  have hn3 : 3 ≤ n := by omega
  refine le_trans ?_ (le_max_left _ _)
  have hc : 0 < cAdopted n := cAdopted_pos hn3
  positivity

/-- **The numeric obligation, discharged**: `SlackHyp` at the adopted constants. -/
theorem slackHyp_adopted (hn : 2073600 ≤ n) :
    SlackHyp n (DriftStopped6.mAdopted n) (DriftStopped6.cAdopted n) (B_adopted n)
      DriftStopped6.slackAdopted := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hC := C₁_le hn
  have hB := B_adopted_le' hn
  have hB0 := B_adopted_nonneg hn
  have hC0 : 0 ≤ C₁ n (DriftStopped6.mAdopted n) (DriftStopped6.cAdopted n) :=
    C₁_nonneg (cAdopted_nonneg hn) (by have := half_le_mAdopted hn; linarith)
  have hsq : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
    nlinarith [Real.sq_sqrt hn0.le, Real.sqrt_nonneg ((n : ℝ)), sqrt_ge_1440 hn]
  have hstep : C₁ n (DriftStopped6.mAdopted n) (DriftStopped6.cAdopted n) * (2 * B_adopted n)
      ≤ (3 * Real.sqrt (n : ℝ)) * (2 * (5 / (n : ℝ) ^ 3)) := by
    refine mul_le_mul hC (by linarith) (by linarith) (by positivity)
  have hfin : (3 * Real.sqrt (n : ℝ)) * (2 * (5 / (n : ℝ) ^ 3)) ≤ 1 := by
    have hn2 : (30 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith [hnR, hn0]
    have hcube : 30 * (n : ℝ) ≤ (n : ℝ) ^ 3 := by nlinarith [hn2, hn0]
    have hval : (3 * Real.sqrt (n : ℝ)) * (2 * (5 / (n : ℝ) ^ 3))
        = 30 * Real.sqrt (n : ℝ) / (n : ℝ) ^ 3 := by ring
    rw [hval, div_le_one (by positivity)]
    linarith
  rw [SlackHyp, DriftStopped6.slackAdopted]
  linarith

/-- **`Brief54Obligation` at the adopted constants, discharged outright.**  `MaximalAtAdopted` is
`GaussianMaximal3.maximalAtAdopted_adopted` and `SlackHyp` is `slackHyp_adopted`; report 56 item 4
recorded that nothing in the tree fixed `m`, `c` or `slack`, and `DriftStopped6` fixes them. -/
theorem brief54Obligation_adopted (hn : 2073600 ≤ n) :
    Brief54Obligation (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))
      (ChainSetup.step (Submission.L10.cAdopted n))
      (DriftStopped6.mAdopted n) (DriftStopped6.cAdopted n) (Submission.L10.B_adopted n)
      DriftStopped6.slackAdopted :=
  ⟨Submission.L10.maximalAtAdopted_adopted (by omega), slackHyp_adopted hn⟩

end Numeric

/-! ## 2. The window the drift side runs on -/

section Window

open Classical in
/-- **`W_g`** — the drift side does not run the chain on the whole shell but on the part of it
that meets the good line, which is exactly the window `Theorem2.LightContact` sums over. -/
noncomputable def windowOf (α : ℝ) (p m : ℕ) (g : Fin (m + 1) → ZMod p) :
    Finset (Fin (m + 1) → ℤ) :=
  (shell α (m + 1)).filter (fun y => y ∈ latZ p (m + 1) g)

theorem mem_windowOf {p m : ℕ} {α : ℝ} {g : Fin (m + 1) → ZMod p} {y : Fin (m + 1) → ℤ} :
    y ∈ windowOf α p m g ↔ y ∈ shell α (m + 1) ∧ y ∈ latZ p (m + 1) g := by
  classical
  rw [windowOf, Finset.mem_filter]

/-- **Any filter of the same predicate is `W_g`** — the decidability instance a caller happens to
carry does not change the `Finset`.  This is what lets `Theorem2.LightContact`'s sum and
`LatticeData.tailSideHyp_latZ`'s window both be read as `windowOf`. -/
theorem filter_eq_windowOf {p m : ℕ} {α : ℝ} {g : Fin (m + 1) → ZMod p}
    (inst : DecidablePred fun y : Fin (m + 1) → ℤ => y ∈ latZ p (m + 1) g) :
    @Finset.filter _ (fun y => y ∈ latZ p (m + 1) g) inst (shell α (m + 1))
      = windowOf α p m g := by
  ext y
  rw [Finset.mem_filter, mem_windowOf]

theorem windowOf_subset {p m : ℕ} {α : ℝ} {g : Fin (m + 1) → ZMod p} :
    windowOf α p m g ⊆ shell α (m + 1) := fun _ hy => (mem_windowOf.1 hy).1

end Window

/-! ## 3. `Theorem3.DriftSide''`, reduced -/

section Residual

/-- **The drift side's residual.**  Everything `Theorem3.DriftSide''` asks for, plus: the light
contact as a sum over `W_g`, the chain's data restricted to `W_g` (three structures), the maximal
obligation at the adopted constants, and the integrability at a random index.  Only
`Assembly.ChainOutput` is owed. -/
def DriftResidual (c₀ : ℝ) : Prop :=
  ∀ m : ℕ, Threshold2.n₁ ≤ m → ∀ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p) (α : ℝ),
    0 < α → ∀ (hn : 3 ≤ m + 1)
      (hraw : RawData p (m + 1) α ((1 - 1 / ((m + 1 : ℕ) : ℝ)) / α)
        (qC α) (shell α (m + 1)) (A0C (m + 1)))
      (hnd : NormData (m + 1) α (qC α) (shell α (m + 1)) (A0C (m + 1)))
      (g : Fin (m + 1) → ZMod p), g ≠ 0 →
      (∀ y : Fin (m + 1) → ℤ, y ≠ 0 →
        ‖toE (m + 1) y‖ ≤ (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α → y ∉ latZ p (m + 1) g) →
      (∑ y ∈ windowOf α p m g, Theorem2.chainW hn hraw hnd y
        < ENNReal.ofReal (64 * C1C α (m + 1))) →
      RawData p (m + 1) α ((1 - 1 / ((m + 1 : ℕ) : ℝ)) / α)
        (qC α) (windowOf α p m g) (A0C (m + 1)) →
      NormData (m + 1) α (qC α) (windowOf α p m g) (A0C (m + 1)) →
      TailSideHyp (m + 1) (Real.sqrt (ParamsAdopted2.stepSizeAdopted2 (m + 1))) α
        (qC α) (windowOf α p m g) (A0C (m + 1)) →
      Brief54Obligation (ChainSetup.gaussPath (EuclideanSpace ℝ (UT (m + 1))))
        (ChainSetup.step (Submission.L10.cAdopted (m + 1)))
        (DriftStopped6.mAdopted (m + 1)) (DriftStopped6.cAdopted (m + 1))
        (Submission.L10.B_adopted (m + 1)) DriftStopped6.slackAdopted →
      IntegrableAtIndex (ChainSetup.gaussPath (EuclideanSpace ℝ (UT (m + 1))))
        (ChainSetup.step (Submission.L10.cAdopted (m + 1)))
        (ParamsAdopted2.numStepsAdopted2 (m + 1)) →
      Assembly.ChainOutput α g c₀

/-- **The reduction.**  Five of the residual's extra inputs are theorems: `LatticeData`'s three
restrictions, `brief54Obligation_adopted`, and `GaussianMaximal3.integrableAtIndex_adopted`.  The
light-contact fact needs no work at all — it *is* the count bound over `W_g`. -/
theorem driftSide''_of_residual {c₀ : ℝ} (h : DriftResidual c₀) : Theorem3.DriftSide'' c₀ := by
  intro m hm p hp hp0 α hα hn hraw hnd g hg hfree hlight
  have hm1 : 2073600 ≤ m + 1 := by
    have h2 : 2073600 ≤ m := by simpa [Threshold2.n₁] using hm
    omega
  have hlight' : ∑ y ∈ windowOf α p m g, Theorem2.chainW hn hraw hnd y
      < ENNReal.ofReal (64 * C1C α (m + 1)) := by
    have hL := hlight
    simp only [Theorem2.LightContact] at hL
    rwa [filter_eq_windowOf] at hL
  have htail : TailSideHyp (m + 1) (Real.sqrt (ParamsAdopted2.stepSizeAdopted2 (m + 1))) α
      (qC α) (windowOf α p m g) (A0C (m + 1)) := by
    have hT := LatticeData.tailSideHyp_latZ hraw hnd hn g
    rwa [filter_eq_windowOf] at hT
  exact h m hm p hp hp0 α hα hn hraw hnd g hg hfree hlight'
    (LatticeData.rawData_mono hraw windowOf_subset)
    (LatticeData.normData_mono hnd windowOf_subset)
    htail
    (brief54Obligation_adopted hm1)
    (Submission.L10.integrableAtIndex_adopted (by omega))

/-- **The challenge statement from the residual alone.** -/
theorem klartag_packing_of_residual {c₀ : ℝ} (hc₀ : 0 < c₀) (h : DriftResidual c₀) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      let V := EuclideanSpace ℝ (Fin (n + 1))
      ∃ φ : V →ₗ[ℝ] V, let E := φ '' Metric.ball (0 : V) 1
        (MeasureTheory.volume E : EReal) = c * n ^ 2 ∧
        {v ∈ E | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} :=
  Theorem3.klartag_packing_of_drift hc₀ (driftSide''_of_residual h)

end Residual

end Submission.L10.DriftStopped7

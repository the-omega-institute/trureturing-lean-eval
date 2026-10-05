/-
Gate L-10 (`klartag_packing`), brief 95 item (4) — the truncated sum's mean from below, summed
over the horizon.

`StepSecondMoment.integral_sqTrunc_ge` is the per-step bound; summing it over `k < K` gives the
`E[G]` that `DriftChargeTotal.driftCen` is built from, and hence the growth that makes `hLb`
survive: `driftCen ≈ κ(1+ε)·E[G] → 4·log n`, cancelling the `−4·log n` on the other side of
`L < C' − 4·log n` exactly.

Nothing reported is edited.  This module is deliberately **not** `StepSecondMoment.lean`, which
already exists and is mirrored.
-/
import Submission.L10.StepSecondMoment
import Submission.L10.DriftChargeTotal

set_option linter.unusedSectionVars false

namespace Submission.L10.TruncSumMean

open MeasureTheory Finset Module Submission.L10 Submission.L10.Increments
open Submission.L10.RawDataInst2

variable {n : ℕ}

/-- **`E[G]` from below.**  `G = ∑_{k<K} min(‖ξ_k‖², cap)`, so the per-step bound sums. -/
theorem integral_sum_sqTrunc_ge {c cap : ℝ} (hcap : 0 < cap) (K : ℕ) :
    (K : ℝ) * (c ^ 2 * (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ)
        - 100 * (c ^ 2) ^ 2 * ((Fintype.card (UT n) : ℝ)) ^ 2 / cap)
      ≤ ∫ ω, (∑ j ∈ Finset.range K, StepTruncVariance.sqTrunc (n := n) c cap j ω)
          ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) := by
  classical
  have hint : ∀ j ∈ Finset.range K,
      Integrable (StepTruncVariance.sqTrunc (n := n) c cap j)
        (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) := by
    intro j _
    refine Integrable.mono' (integrable_const cap)
      (StepTruncVariance.measurable_sqTrunc c cap j).aestronglyMeasurable ?_
    filter_upwards with ω
    have h := StepTruncVariance.sqTrunc_mem_Icc (n := n) (c := c) hcap.le j ω
    rw [Real.norm_eq_abs, abs_of_nonneg h.1]; exact h.2
  rw [integral_finsetSum _ hint]
  calc (K : ℝ) * (c ^ 2 * (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ)
        - 100 * (c ^ 2) ^ 2 * ((Fintype.card (UT n) : ℝ)) ^ 2 / cap)
      = ∑ _j ∈ Finset.range K, (c ^ 2 * (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ)
          - 100 * (c ^ 2) ^ 2 * ((Fintype.card (UT n) : ℝ)) ^ 2 / cap) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ ∑ j ∈ Finset.range K, ∫ ω, StepTruncVariance.sqTrunc (n := n) c cap j ω
          ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) :=
        Finset.sum_le_sum fun j _ => StepSecondMoment.integral_sqTrunc_ge hcap j

/-- **`driftCen` from below.**  The shape `hLb` consumes: the centre is at least
`κ(1+ε)` times the summed lower bound, the `(1+1/ε)(c₃η)²` piece being non-negative. -/
theorem driftCen_ge {c cap κ ε c₃ η : ℝ} (hcap : 0 < cap) (hκ : 0 ≤ κ) (hε : 0 < ε) (K : ℕ)
    (hcapeq : cap = η ^ 2) :
    κ * ((1 + ε) * ((K : ℝ) * (c ^ 2 * (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ)
          - 100 * (c ^ 2) ^ 2 * ((Fintype.card (UT n) : ℝ)) ^ 2 / cap)))
      ≤ DriftChargeTotal.driftCen (n := n) c η c₃ κ ε K := by
  subst hcapeq
  rw [DriftChargeTotal.driftCen]
  have hG := integral_sum_sqTrunc_ge (n := n) (c := c) hcap K
  have h1 : (0 : ℝ) ≤ 1 + ε := by linarith
  have hmul : (1 + ε) * ((K : ℝ) * (c ^ 2 * (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ)
        - 100 * (c ^ 2) ^ 2 * ((Fintype.card (UT n) : ℝ)) ^ 2 / η ^ 2))
      ≤ (1 + ε) * (∫ ω, (∑ j ∈ Finset.range K,
          StepTruncVariance.sqTrunc (n := n) c (η ^ 2) j ω)
        ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))) :=
    mul_le_mul_of_nonneg_left hG h1
  have hrest : (0 : ℝ) ≤ (1 + 1 / ε) * (c₃ * η) ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left (by linarith : (1 + ε) * ((K : ℝ) * (c ^ 2
      * (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ)
      - 100 * (c ^ 2) ^ 2 * ((Fintype.card (UT n) : ℝ)) ^ 2 / η ^ 2))
    ≤ (1 + ε) * (∫ ω, (∑ j ∈ Finset.range K,
        StepTruncVariance.sqTrunc (n := n) c (η ^ 2) j ω)
      ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))) + (1 + 1 / ε) * (c₃ * η) ^ 2) hκ
  linarith


/-! ## At the adopted parameters -/

section Adopted

/-- `η² = 2·h·dim·n` at the adopted parameters. -/
theorem etaAdopted_sq (hn : 3 ≤ n) :
    DriftStopped6.etaAdopted n ^ 2
      = 2 * ParamsAdopted2.stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ) * (n : ℝ) := by
  rw [DriftStopped6.etaAdopted]
  refine Real.sq_sqrt ?_
  have := (TailSideSetup2.stepSizeAdopted2_pos hn).le
  positivity

theorem cAdopted_sq (hn : 3 ≤ n) :
    Submission.L10.cAdopted n ^ 2 = ParamsAdopted2.stepSizeAdopted2 n := by
  rw [Submission.L10.cAdopted]
  exact Real.sq_sqrt (TailSideSetup2.stepSizeAdopted2_pos hn).le

/-- **`driftCen ≥ κ(1+ε)·T·dim·(1 − 50/n)`** at the adopted parameters — the growth that cancels
the `−4·log n` of `hLb`, since `T·dim = 8·log n·(1+1/n)` and `κ → 1/2`. -/
theorem driftCen_ge_adopted (hn : 3 ≤ n) {κ ε c₃ : ℝ} (hκ : 0 ≤ κ) (hε : 0 < ε) :
    κ * ((1 + ε) * (ChainDrift.horizon n * (Fintype.card (UT n) : ℝ) * (1 - 50 / (n : ℝ))))
      ≤ DriftChargeTotal.driftCen (n := n) (Submission.L10.cAdopted n)
          (DriftStopped6.etaAdopted n) c₃ κ ε (ParamsAdopted2.numStepsAdopted2 n) := by
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
  have hcsq := cAdopted_sq (n := n) hn
  have hesq := etaAdopted_sq (n := n) hn
  have hcap : (0 : ℝ) < DriftStopped6.etaAdopted n ^ 2 := by rw [hesq]; positivity
  have hfr : (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) = (Fintype.card (UT n) : ℝ) := by
    rw [finrank_euclideanSpace]
  have hNh := ParamsAdopted2.numStepsAdopted2_mul_stepSizeAdopted2 hn
  have hbase := driftCen_ge (n := n) (c := Submission.L10.cAdopted n)
    (cap := DriftStopped6.etaAdopted n ^ 2) (κ := κ) (ε := ε) (c₃ := c₃)
    (η := DriftStopped6.etaAdopted n) hcap hκ hε (ParamsAdopted2.numStepsAdopted2 n) rfl
  refine le_trans (le_of_eq ?_) hbase
  have hkey : ((ParamsAdopted2.numStepsAdopted2 n : ℕ) : ℝ)
        * (Submission.L10.cAdopted n ^ 2 * (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ)
          - 100 * (Submission.L10.cAdopted n ^ 2) ^ 2 * ((Fintype.card (UT n) : ℝ)) ^ 2
            / DriftStopped6.etaAdopted n ^ 2)
      = ChainDrift.horizon n * (Fintype.card (UT n) : ℝ) * (1 - 50 / (n : ℝ)) := by
    rw [hcsq, hfr, hesq]
    field_simp
    nlinarith [hNh, hh0, hD, hn0]
  rw [hkey]


/-- **`T·dim ≥ 8·log n`** — the drift scale, from below.  `horizon n = 16·log n/n²` and
`card (UT n) = n(n+1)/2`, so the product is `8·log n·(n+1)/n`.  With `κ ≥ 1/2` and `1 + ε ≥ 1`,
`driftCen_ge_adopted` then gives `driftCen ≥ 4·log n·(1 − 50/n)`, which is exactly what `hLb`
needs against the `−4·log n` on the other side. -/
theorem horizon_mul_card_ge (hn : 3 ≤ n) :
    8 * Real.log n ≤ ChainDrift.horizon n * (Fintype.card (UT n) : ℝ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hlog : (1 : ℝ) ≤ Real.log n := ChainDrift.log_pos_of_three hn
  have hcard : (Fintype.card (UT n) : ℝ) = (n : ℝ) * ((n : ℝ) + 1) / 2 := by
    rw [ChainWiring.card_UT]
    obtain ⟨t, ht⟩ := Nat.even_mul_succ_self n
    have ht2 : n * (n + 1) = 2 * t := by omega
    rw [ht2, Nat.mul_div_cancel_left t (by norm_num)]
    have hcast : ((n : ℝ)) * ((n : ℝ) + 1) = 2 * (t : ℝ) := by
      have := congrArg (fun k : ℕ => (k : ℝ)) ht2
      push_cast at this
      linarith
    linarith
  rw [ChainDrift.horizon, hcard]
  have hkey : 16 * Real.log n / (n : ℝ) ^ 2 * ((n : ℝ) * ((n : ℝ) + 1) / 2)
      = 8 * Real.log n * (((n : ℝ) + 1) / (n : ℝ)) := by
    field_simp; ring
  rw [hkey]
  have hfrac : (1 : ℝ) ≤ ((n : ℝ) + 1) / (n : ℝ) := by
    rw [le_div_iff₀ hn0]; linarith
  nlinarith [hlog, hfrac]


/-! ## `hLb`, from the two bounds above -/

/-- **`hLb`**, the first of item (4)'s two numeric facts.  `L = logDet A₀ − (driftCen + s') − t`
and the right-hand side of `L < C' − 4·log n` decreases in `n`, so the inequality lives or dies on
`driftCen` growing at the same rate.  It does: `driftCen ≥ κ(1+ε)·T·dim·(1 − 50/n) ≥ 4·log n −
200·log n/n`, and the two `4·log n` cancel, leaving `logDet A₀ + 200·log n/n < C'` — true with five
orders to spare.

The two remaining hypotheses are pure arithmetic about the adopted constants: `κ ≥ 1/2` (i.e.
`mAt ≤ 1`, since `κ = (1/2 + 2rr)/mAt²`) and a crude ceiling on `200·log n/n`. -/
theorem hLb_of_bounds (hn : 3 ≤ n) {κ ε c₃ C' s' t : ℝ}
    (hκ : 1 / 2 ≤ κ) (hκ0 : 0 ≤ κ) (hε : 0 < ε) (hs' : 0 ≤ s') (ht : 0 ≤ t)
    (hloss : 50 / (n : ℝ) ≤ 1)
    (hA0 : ChainWiring.logDet (A0C n) ≤ 3)
    (hsmall : 200 * Real.log n / (n : ℝ) ≤ 100)
    (hC : 500000 ≤ C') :
    ChainWiring.logDet (A0C n)
        - (DriftChargeTotal.driftCen (n := n) (Submission.L10.cAdopted n)
            (DriftStopped6.etaAdopted n) c₃ κ ε (ParamsAdopted2.numStepsAdopted2 n) + s') - t
      < C' - 4 * Real.log n := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hlog : (1 : ℝ) ≤ Real.log n := ChainDrift.log_pos_of_three hn
  have hcen := driftCen_ge_adopted (n := n) hn (κ := κ) (ε := ε) (c₃ := c₃) hκ0 hε
  have hTd := horizon_mul_card_ge (n := n) hn
  have hfac : (0 : ℝ) ≤ 1 - 50 / (n : ℝ) := by linarith
  -- `κ(1+ε)·T·dim·(1−50/n) ≥ 4·log n − 200·log n/n`
  have hstep : 4 * Real.log n - 200 * Real.log n / (n : ℝ)
      ≤ κ * ((1 + ε) * (ChainDrift.horizon n * (Fintype.card (UT n) : ℝ)
          * (1 - 50 / (n : ℝ)))) := by
    have h1 : 8 * Real.log n * (1 - 50 / (n : ℝ))
        ≤ ChainDrift.horizon n * (Fintype.card (UT n) : ℝ) * (1 - 50 / (n : ℝ)) :=
      mul_le_mul_of_nonneg_right hTd hfac
    have h2 : 8 * Real.log n * (1 - 50 / (n : ℝ))
        ≤ (1 + ε) * (ChainDrift.horizon n * (Fintype.card (UT n) : ℝ)
            * (1 - 50 / (n : ℝ))) := by
      have hnn : (0 : ℝ) ≤ ChainDrift.horizon n * (Fintype.card (UT n) : ℝ)
          * (1 - 50 / (n : ℝ)) := by
        have : (0 : ℝ) ≤ 8 * Real.log n * (1 - 50 / (n : ℝ)) := by positivity
        linarith
      nlinarith [h1, hnn, hε]
    have h3 : (1 / 2) * (8 * Real.log n * (1 - 50 / (n : ℝ)))
        ≤ κ * ((1 + ε) * (ChainDrift.horizon n * (Fintype.card (UT n) : ℝ)
            * (1 - 50 / (n : ℝ)))) := by
      have hnn2 : (0 : ℝ) ≤ 8 * Real.log n * (1 - 50 / (n : ℝ)) := by positivity
      nlinarith [h2, hκ, hnn2]
    have hid : (1 / 2) * (8 * Real.log n * (1 - 50 / (n : ℝ)))
        = 4 * Real.log n - 200 * Real.log n / (n : ℝ) := by
      field_simp; ring
    linarith [h3, hid.le, hid.ge]
  linarith [hcen, hstep, hA0, hsmall, hC, hs', ht]


/-- **`E[G]` from above**, the companion `hbudget` needs: the truncation only lowers, so
`∫ min(‖ξ_k‖², cap) ≤ ∫ ‖ξ_k‖² = c²·dim`, and summing gives `K·c²·dim = T·dim` at `K = N`. -/
theorem integral_sum_sqTrunc_le (_hn : 3 ≤ n) {c cap : ℝ} (hcap : 0 < cap) (K : ℕ) :
    ∫ ω, (∑ j ∈ Finset.range K, StepTruncVariance.sqTrunc (n := n) c cap j ω)
        ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))
      ≤ (K : ℝ) * (c ^ 2 * (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ)) := by
  classical
  have hint : ∀ j ∈ Finset.range K,
      Integrable (StepTruncVariance.sqTrunc (n := n) c cap j)
        (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) := by
    intro j _
    refine Integrable.mono' (integrable_const cap)
      (StepTruncVariance.measurable_sqTrunc c cap j).aestronglyMeasurable ?_
    filter_upwards with ω
    have h := StepTruncVariance.sqTrunc_mem_Icc (n := n) (c := c) hcap.le j ω
    rw [Real.norm_eq_abs, abs_of_nonneg h.1]; exact h.2
  rw [integral_finsetSum _ hint]
  have hstep : ∀ j ∈ Finset.range K,
      ∫ ω, StepTruncVariance.sqTrunc (n := n) c cap j ω
          ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))
        ≤ c ^ 2 * (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) := by
    intro j hj
    have h2i : Integrable (fun ω => ‖ChainSetup.step (ι := UT n) c j ω‖ ^ 2)
        (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) :=
      ChainSetup.integrable_norm_sq_step c j
    have hmono := integral_mono (hint j hj) h2i
      (fun ω => StepTruncVariance.sqTrunc_le (n := n) (c := c) (cap := cap) j ω)
    rw [StepSecondMoment.integral_norm_step_sq] at hmono
    exact hmono
  calc ∑ j ∈ Finset.range K, ∫ ω, StepTruncVariance.sqTrunc (n := n) c cap j ω
        ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))
      ≤ ∑ _j ∈ Finset.range K, c ^ 2 * (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) :=
        Finset.sum_le_sum hstep
    _ = (K : ℝ) * (c ^ 2 * (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end Adopted




end Submission.L10.TruncSumMean


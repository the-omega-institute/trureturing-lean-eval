import Mathlib
import Submission.L10.ChainDataInst
import Submission.L10.ChainInputDom
import Submission.L10.ChainDrift

/-!
# Gate L-10 — the contact count the drift actually consumes: the **time-integrated** one

Brief 39.  Report 37's `hitting_tail_forces_zero` shows a hitting-probability weight cannot be
dominated by the `t`-integrated profile, so `ChainDataInst.expected_card_le` (terminal count,
hitting probability at `T`) and the weight §5's Use 2 consumes are two different quantities.
This module states the one the drift wants.

The drift consumes the free dimension **per step** (`ChainDrift.logdet_bound`'s `hN`), so the
quantity that matters is `Σ_k h·|C_k|`, Klartag's `∫₀ᵀ K_t dt` of eq. (66) — not `|C_N|`.

* `intWeight` — the weight, defined: the discrete `∫₀ᵀ P(x ∈ C_t) dt`.
* `integrated_count_eq` — **the identification**, an equality by Tonelli over two finite sums.
* `integrated_count_le` — from Proposition 4.1 at each horizon, `≤ 4·Σ_x (integrated profile)`.
* `sum_free_ge` — `hN` in the only shape the contact bound supplies: a bound on the sum.
* `logdet_bound_sum` — `ChainDrift.logdet_bound` with `hN` replaced by that summed hypothesis.

The factor `4` is `Padding.padded_tail_of_increments`'s; it is absorbed into `w`, not into the
scale — see the report.  Everything is stated for an abstract window and contact set (rule 7).
-/

open MeasureTheory Finset

namespace Submission.L10.ContactIntegrated

variable {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]

/-! ### 1. The identification -/

/-- **The weight §5's Use 2 consumes**: the discrete `∫₀ᵀ P(x ∈ C_t) dt`, a Riemann sum of the
per-time contact probability over the `Nsteps` steps of size `hstep`.  *Not* the hitting
probability at `T` — report 37's `hitting_tail_forces_zero` refutes that reading. -/
noncomputable def intWeight (μ : Measure Ω) (Cset : ℕ → Ω → Finset ι) (hstep : ℝ)
    (Nsteps : ℕ) (x : ι) : ℝ :=
  ∑ k ∈ range Nsteps, hstep * μ.real {ω | x ∈ Cset k ω}

/-- The expected contact count at one step is the window sum of per-time contact probabilities. -/
theorem integral_card_eq (μ : Measure Ω) [IsProbabilityMeasure μ] (W : Finset ι)
    (Cs : Ω → Finset ι) (hsub : ∀ ω, Cs ω ⊆ W)
    (hmeas : ∀ x ∈ W, MeasurableSet {ω | x ∈ Cs ω}) :
    ∫ ω, ((Cs ω).card : ℝ) ∂μ = ∑ x ∈ W, μ.real {ω | x ∈ Cs ω} := by
  classical
  have hcard : ∀ ω, ((Cs ω).card : ℝ)
      = ∑ x ∈ W, Set.indicator {ω | x ∈ Cs ω} (fun _ => (1 : ℝ)) ω := by
    intro ω
    have hfil : W.filter (fun x => x ∈ Cs ω) = Cs ω := by
      ext x; simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨hsub ω h, h⟩⟩
    rw [← hfil, Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases hx : x ∈ Cs ω <;> simp [Set.indicator, hx]
  have hint : ∀ x ∈ W, Integrable
      (fun ω => Set.indicator {ω | x ∈ Cs ω} (fun _ => (1 : ℝ)) ω) μ :=
    fun x hx => (integrable_const (1 : ℝ)).indicator (hmeas x hx)
  calc ∫ ω, ((Cs ω).card : ℝ) ∂μ
      = ∫ ω, ∑ x ∈ W, Set.indicator {ω | x ∈ Cs ω} (fun _ => (1 : ℝ)) ω ∂μ := by simp_rw [hcard]
    _ = ∑ x ∈ W, ∫ ω, Set.indicator {ω | x ∈ Cs ω} (fun _ => (1 : ℝ)) ω ∂μ :=
        integral_finsetSum W hint
    _ = ∑ x ∈ W, μ.real {ω | x ∈ Cs ω} :=
        Finset.sum_congr rfl (fun x hx => integral_indicator_one (hmeas x hx))

/-- **Tonelli for the two finite sums.**  The time-integrated expected contact count *is* the
window sum of the integrated weights — an equality, not a bound.  This is the identification
report 37 says no module states: `Σ_k h·E|C_k| = Σ_x ∫₀ᵀ P(x ∈ C_t) dt`. -/
theorem integrated_count_eq (μ : Measure Ω) [IsProbabilityMeasure μ] (W : Finset ι)
    (Cset : ℕ → Ω → Finset ι) (hstep : ℝ) (Nsteps : ℕ)
    (hsub : ∀ k ω, Cset k ω ⊆ W)
    (hmeas : ∀ k, ∀ x ∈ W, MeasurableSet {ω | x ∈ Cset k ω}) :
    ∑ k ∈ range Nsteps, hstep * ∫ ω, ((Cset k ω).card : ℝ) ∂μ
      = ∑ x ∈ W, intWeight μ Cset hstep Nsteps x := by
  simp_rw [intWeight]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [integral_card_eq μ W (Cset k) (hsub k) (hmeas k), Finset.mul_sum]

/-! ### 2. `integrated_count_le` from `ChainRaw.tail` at each horizon -/

/-- **`integrated_count_le`.**  With Proposition 4.1 at each horizon — the per-time contact
probability below `4·(profile at that time)`, the factor 4 of
`Padding.padded_tail_of_increments` — the time-integrated contact count is below `4` times the
window sum of the integrated profile. -/
theorem integrated_count_le (μ : Measure Ω) [IsProbabilityMeasure μ] (W : Finset ι)
    (Cset : ℕ → Ω → Finset ι) {hstep : ℝ} (hstep0 : 0 ≤ hstep) (Nsteps : ℕ)
    (hsub : ∀ k ω, Cset k ω ⊆ W)
    (hmeas : ∀ k, ∀ x ∈ W, MeasurableSet {ω | x ∈ Cset k ω})
    (prof : ι → ℕ → ℝ)
    (htail : ∀ k, k < Nsteps → ∀ x ∈ W, μ.real {ω | x ∈ Cset k ω} ≤ 4 * prof x k) :
    ∑ k ∈ range Nsteps, hstep * ∫ ω, ((Cset k ω).card : ℝ) ∂μ
      ≤ 4 * ∑ x ∈ W, ∑ k ∈ range Nsteps, hstep * prof x k := by
  rw [integrated_count_eq μ W Cset hstep Nsteps hsub hmeas, Finset.mul_sum]
  refine Finset.sum_le_sum (fun x hx => ?_)
  rw [intWeight, Finset.mul_sum]
  refine Finset.sum_le_sum (fun k hk => ?_)
  have h1 : μ.real {ω | x ∈ Cset k ω} ≤ 4 * prof x k :=
    htail k (Finset.mem_range.1 hk) x hx
  calc hstep * μ.real {ω | x ∈ Cset k ω} ≤ hstep * (4 * prof x k) :=
        mul_le_mul_of_nonneg_left h1 hstep0
    _ = 4 * (hstep * prof x k) := by ring

/-! ### 3. The drift side: `hN` discharged from the integrated count -/

/-- **The summed free dimension.**  `N_k ≥ d − |C_k|` (`Chain.finrank_freeSub_ge_card`), so the
summed expected free dimension is at least `N·d` less the integrated contact count — which
`integrated_count_le` bounds.  This is `ChainDrift.logdet_bound`'s `hN`, in the only form the
contact bound can supply: a bound on the **sum**, not a uniform per-step bound. -/
theorem sum_free_ge (μ : Measure Ω) [IsProbabilityMeasure μ] (W : Finset ι)
    (Cset : ℕ → Ω → Finset ι) (Nfun : ℕ → Ω → ℝ) (d Nsteps : ℕ)
    (hsub : ∀ k ω, Cset k ω ⊆ W)
    (hmeas : ∀ k, ∀ x ∈ W, MeasurableSet {ω | x ∈ Cset k ω})
    (hfree : ∀ k, k < Nsteps → ∀ ω, (d : ℝ) - ((Cset k ω).card : ℝ) ≤ Nfun k ω)
    (hintN : ∀ k, k < Nsteps → Integrable (Nfun k) μ)
    (hintC : ∀ k, k < Nsteps → Integrable (fun ω => ((Cset k ω).card : ℝ)) μ)
    (prof : ι → ℕ → ℝ)
    (htail : ∀ k, k < Nsteps → ∀ x ∈ W, μ.real {ω | x ∈ Cset k ω} ≤ 4 * prof x k) :
    (Nsteps : ℝ) * (d : ℝ) - 4 * (∑ x ∈ W, ∑ k ∈ range Nsteps, prof x k)
      ≤ ∑ k ∈ range Nsteps, ∫ ω, Nfun k ω ∂μ := by
  have hcount : ∑ k ∈ range Nsteps, ∫ ω, ((Cset k ω).card : ℝ) ∂μ
      ≤ 4 * ∑ x ∈ W, ∑ k ∈ range Nsteps, prof x k := by
    have h := integrated_count_le μ W Cset (hstep := 1) zero_le_one Nsteps hsub hmeas prof htail
    simpa using h
  have hstepwise : ∀ k ∈ range Nsteps,
      (d : ℝ) - ∫ ω, ((Cset k ω).card : ℝ) ∂μ ≤ ∫ ω, Nfun k ω ∂μ := by
    intro k hk
    have hk' := Finset.mem_range.1 hk
    have hmono : ∫ ω, ((d : ℝ) - ((Cset k ω).card : ℝ)) ∂μ ≤ ∫ ω, Nfun k ω ∂μ :=
      integral_mono ((integrable_const _).sub (hintC k hk')) (hintN k hk') (hfree k hk')
    rw [integral_sub (integrable_const _) (hintC k hk'), integral_const] at hmono
    simpa using hmono

  have hsplit : ∑ k ∈ range Nsteps, ((d : ℝ) - ∫ ω, ((Cset k ω).card : ℝ) ∂μ)
      = (Nsteps : ℝ) * (d : ℝ) - ∑ k ∈ range Nsteps, ∫ ω, ((Cset k ω).card : ℝ) ∂μ := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  calc (Nsteps : ℝ) * (d : ℝ) - 4 * (∑ x ∈ W, ∑ k ∈ range Nsteps, prof x k)
      ≤ (Nsteps : ℝ) * (d : ℝ) - ∑ k ∈ range Nsteps, ∫ ω, ((Cset k ω).card : ℝ) ∂μ := by
        linarith
    _ = ∑ k ∈ range Nsteps, ((d : ℝ) - ∫ ω, ((Cset k ω).card : ℝ) ∂μ) := hsplit.symm
    _ ≤ ∑ k ∈ range Nsteps, ∫ ω, Nfun k ω ∂μ := Finset.sum_le_sum hstepwise

omit [MeasurableSpace Ω] in
/-- **`ChainDrift.logdet_bound` with the summed hypothesis.**  `logdet_bound` takes a *uniform*
per-step lower bound `b ≤ E[N_k]`; `sum_free_ge` supplies only the sum.  Same conclusion, proved
from `ChainDrift.drift_bound` and `ChainDrift.sum_err_le`; `ChainDrift.lean` is reported and is
not edited (rule 5). -/
theorem logdet_bound_sum {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : ℕ → MeasurableSpace Ω} {D Nf err : ℕ → Ω → ℝ} {κ : ℝ} {m : ℕ}
    (h : ChainDrift.DriftInputs μ ℱ D Nf err κ m) (hκ : 0 ≤ κ)
    {S ε : ℝ} {F : ℕ} {P : ℕ → Prop} [DecidablePred P]
    (hS : S ≤ ∑ k ∈ range m, ∫ ω, Nf k ω ∂μ)
    (hzero : ∀ k, k < m → ¬ P k → ∫ ω, err k ω ∂μ ≤ 0)
    (hbd : ∀ k, k < m → ∫ ω, err k ω ∂μ ≤ ε) (hε : 0 ≤ ε)
    (hcard : ((range m).filter P).card ≤ F) :
    ∫ ω, D m ω ∂μ ≤ ∫ ω, D 0 ω ∂μ - κ * S + (F : ℝ) * ε := by
  have hmain := ChainDrift.drift_bound h
  have hdrift : κ * S ≤ ∑ k ∈ range m, κ * ∫ ω, Nf k ω ∂μ := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hS hκ
  have herr : ∑ k ∈ range m, ∫ ω, err k ω ∂μ ≤ (F : ℝ) * ε :=
    ChainDrift.sum_err_le hzero hbd hε hcard
  linarith

end Submission.L10.ContactIntegrated

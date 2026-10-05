import Mathlib
import Submission.L10.Chain

/-!
# Gate L-10 (`klartag_packing`) — the drift accounting

Brief 7, goal 3.  Klartag's Lemma 3.3 (p. 14-15) and Proposition 3.4 (p. 15-16) in discrete form.

The continuous proof runs Itô's formula for `log det`, bounds the drift by
`δ_t ≥ Tr[π_t]/‖A_t‖²_op`, and argues that the stochastic integral is a true martingale.  In the
discrete chain there is no limit to take, so:

* **Itô ⟶ summation.**  The one-step inequality is `Submission.L10.log_det_add_le` (brief 2);
  conditioning on `ℱ_k` kills its middle term because `ξ_k` is centred and independent of `ℱ_k`.
  Summing over `k` *is* the Riemann sum: `telescope` below.
* **The local-martingale step (hinge 1's C4) disappears entirely.**  Nothing in this file
  integrates a stochastic integral; `integral_step` is `integral_condExp` plus `integral_mono_ae`.
* **Proposition 3.4's two ingredients are separated**: the *dimension count*
  `N_k ≥ dim E - |q(C_k)|` (proved in `Chain.lean` as `finrank_freeSub_ge`) and the *freeze
  count* `≤ dim E` (`Chain.card_freezes_le`), which together bound the telescoped sum from below
  (`sum_ge_of_le`), and the *discretisation error*, which is non-zero only at freeze steps and is
  therefore bounded by (number of freezes) × (worst single overshoot) — `sum_err_le`.

Everything analytic is a **hypothesis**.  `DriftInputs` names them with their exact signatures;
the report lists which brief owns each.

## Main results

* `telescope` — the telescoped drift bound for real sequences.
* `sum_ge_of_le`, `sum_err_le` — the two counting bounds.
* `integral_step` — conditional inequality ⟹ inequality of expectations.
* `drift_bound`, `logdet_bound` — Proposition 3.4's shape, fully proved from `DriftInputs`.
* `horizon`, `numSteps`, `stepSize`, `tradeoff`, `stepSize_le`, `proj_error_le` — the parameters
  `T = 16 log n / n²`, `N`, `h = T/N`, the pinned trade-off `n²T/4 = 4 log n`, and the
  discretisation-error budget.
-/

set_option linter.unusedSectionVars false

namespace Submission.L10.ChainDrift

open MeasureTheory Finset
open scoped ENNReal

/-! ## 1. Telescoping -/

/-- **The telescoped drift bound.**  A one-step decrease with an error term sums to a bound on the
terminal value.  This is the discrete Riemann sum that replaces `-(1/2)∫₀^T δ_s ds`. -/
theorem telescope {D drift err : ℕ → ℝ} {m : ℕ}
    (hstep : ∀ k, k < m → D (k + 1) ≤ D k - drift k + err k) :
    D m ≤ D 0 - ∑ k ∈ range m, drift k + ∑ k ∈ range m, err k := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 := ih fun k hk => hstep k (hk.trans (Nat.lt_succ_self m))
    have h2 := hstep m (Nat.lt_succ_self m)
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    linarith

/-! ## 2. The two counting bounds -/

/-- The drift sum is bounded below by `m` times the worst dimension.  With
`b = dim E - |q(C_m)|` (Chain.finrank_freeSub_ge) this is Klartag's
`∫₀^T E[N_t] dt ≥ T(n(n+1)/2 - |∂E∩L|/2)`. -/
theorem sum_ge_of_le {N : ℕ → ℝ} {b : ℝ} {m : ℕ} (hN : ∀ k, k < m → b ≤ N k) :
    (m : ℝ) * b ≤ ∑ k ∈ range m, N k := by
  calc (m : ℝ) * b = ∑ _k ∈ range m, b := by rw [Finset.sum_const, Finset.card_range]; ring
    _ ≤ ∑ k ∈ range m, N k :=
        Finset.sum_le_sum fun k hk => hN k (Finset.mem_range.1 hk)

/-- **The discretisation error is paid only at freezes.**  If `err k ≤ 0` off the freeze set and
`err k ≤ ε` everywhere, then the total error is at most (freeze count) × `ε`. -/
theorem sum_err_le {err : ℕ → ℝ} {P : ℕ → Prop} [DecidablePred P] {ε : ℝ} {m F : ℕ}
    (hzero : ∀ k, k < m → ¬ P k → err k ≤ 0) (hbd : ∀ k, k < m → err k ≤ ε) (hε : 0 ≤ ε)
    (hcard : ((range m).filter P).card ≤ F) :
    ∑ k ∈ range m, err k ≤ (F : ℝ) * ε := by
  have hsplit : ∑ k ∈ (range m).filter P, err k
      + ∑ k ∈ (range m).filter (fun k => ¬ P k), err k = ∑ k ∈ range m, err k :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have h1 : ∑ k ∈ (range m).filter P, err k ≤ (((range m).filter P).card : ℝ) * ε := by
    calc ∑ k ∈ (range m).filter P, err k ≤ ∑ _k ∈ (range m).filter P, ε :=
          Finset.sum_le_sum fun k hk => hbd k (Finset.mem_range.1 (Finset.mem_filter.1 hk).1)
      _ = (((range m).filter P).card : ℝ) * ε := by rw [Finset.sum_const]; ring
  have h2 : ∑ k ∈ (range m).filter (fun k => ¬ P k), err k ≤ 0 := by
    refine Finset.sum_nonpos fun k hk => ?_
    rw [Finset.mem_filter] at hk
    exact hzero k (Finset.mem_range.1 hk.1) hk.2
  have h3 : (((range m).filter P).card : ℝ) * ε ≤ (F : ℝ) * ε := by
    have : (((range m).filter P).card : ℝ) ≤ (F : ℝ) := by exact_mod_cast hcard
    nlinarith
  linarith

/-! ## 3. The conditional-to-integrated bridge

Hinge 1's step C4 — "the local martingale is a true martingale" (Klartag p. 15, eq. 42, proved
there from Corollary 3.2 and `det A_t ≥ c_L`) — becomes this one lemma, which needs no
integrability beyond that of the two sides. -/

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- If a conditional expectation is dominated a.e., the expectations are ordered. -/
theorem integral_le_of_condExp_le {m : MeasurableSpace Ω} (hm : m ≤ m0) [IsFiniteMeasure μ]
    {f g : Ω → ℝ} (_hf : Integrable f μ) (hg : Integrable g μ)
    (h : μ[f|m] ≤ᵐ[μ] g) : ∫ ω, f ω ∂μ ≤ ∫ ω, g ω ∂μ := by
  have h1 : ∫ ω, (μ[f|m]) ω ∂μ = ∫ ω, f ω ∂μ := integral_condExp hm
  rw [← h1]
  exact integral_mono_ae integrable_condExp hg h

/-! ## 4. The drift inputs, and the assembled bound -/

/-- **The analytic inputs of the drift accounting**, with their exact signatures.

`D k = log det A_k`, `N k = N_k = dim F(C_k)`, `err k` the discretisation cost of the freeze at
step `k`, `κ = h/(2 ‖A‖²_op κ²)` the per-step drift rate, `ℱ` the filtration.  The report names
which brief owns each field; `step` is the one that consumes brief 2's `log_det_add_le` and
brief 6's conditional law of `π_k ξ_k`. -/
structure DriftInputs (μ : Measure Ω) (ℱ : ℕ → MeasurableSpace Ω) (D N err : ℕ → Ω → ℝ)
    (κ : ℝ) (m : ℕ) : Prop where
  /-- the filtration is coarser than the ambient σ-algebra -/
  le : ∀ k, ℱ k ≤ m0
  /-- **the one-step conditional inequality** (briefs 2 and 6) -/
  step : ∀ k, k < m → μ[D (k + 1)|ℱ k] ≤ᵐ[μ] fun ω => D k ω - κ * N k ω + err k ω
  intD : ∀ k, k ≤ m → Integrable (D k) μ
  intN : ∀ k, k < m → Integrable (N k) μ
  interr : ∀ k, k < m → Integrable (err k) μ

variable {ℱ : ℕ → MeasurableSpace Ω} {D N err : ℕ → Ω → ℝ} {κ : ℝ} {m : ℕ}

/-- One step, integrated. -/
theorem integral_step [IsFiniteMeasure μ] (h : DriftInputs μ ℱ D N err κ m) {k : ℕ}
    (hk : k < m) :
    ∫ ω, D (k + 1) ω ∂μ ≤ ∫ ω, D k ω ∂μ - κ * ∫ ω, N k ω ∂μ + ∫ ω, err k ω ∂μ := by
  have hint1 : Integrable (fun ω => D k ω - κ * N k ω) μ :=
    (h.intD k hk.le).sub ((h.intN k hk).const_mul κ)
  have hint : Integrable (fun ω => D k ω - κ * N k ω + err k ω) μ := hint1.add (h.interr k hk)
  have hmain := integral_le_of_condExp_le (h.le k) (h.intD (k + 1) hk) hint (h.step k hk)
  have heq : ∫ ω, (D k ω - κ * N k ω + err k ω) ∂μ
      = ∫ ω, D k ω ∂μ - κ * ∫ ω, N k ω ∂μ + ∫ ω, err k ω ∂μ := by
    rw [integral_add hint1 (h.interr k hk),
      integral_sub (h.intD k hk.le) ((h.intN k hk).const_mul κ), integral_const_mul]
  rwa [heq] at hmain

/-- **The telescoped drift bound, integrated** (Klartag Lemma 3.3, discrete form). -/
theorem drift_bound [IsFiniteMeasure μ] (h : DriftInputs μ ℱ D N err κ m) :
    ∫ ω, D m ω ∂μ ≤ ∫ ω, D 0 ω ∂μ - ∑ k ∈ range m, κ * ∫ ω, N k ω ∂μ
      + ∑ k ∈ range m, ∫ ω, err k ω ∂μ :=
  telescope (D := fun k => ∫ ω, D k ω ∂μ) fun _k hk => integral_step h hk

/-- **Proposition 3.4's shape.**  With

* `hN` : `b ≤ E[N_k]` for every `k < m` — supplied by `Chain.finrank_freeSub_ge` together with a
  bound on the expected contact count (`b = dim E - E|q(C_m)|`);
* `hzero`/`hbd`/`hcard` : the discretisation error is paid at most `F` times, at most `ε` each —
  supplied by `Chain.card_freezes_le` (`F = finrank ℝ E`) and the per-freeze overshoot bound,

the terminal log-determinant obeys `E log det A_m ≤ E log det A_0 - κ m b + F ε`.  With
`κ m = T/2·‖A‖⁻²`, `b = n(n+1)/2 - E|∂E ∩ L|`, this is
`E log det A_T ≤ n log a₀ - n²T/4 + (T/2)·E|∂E∩L| + Fε`. -/
theorem logdet_bound [IsFiniteMeasure μ] (h : DriftInputs μ ℱ D N err κ m) (hκ : 0 ≤ κ)
    {b ε : ℝ} {F : ℕ} {P : ℕ → Prop} [DecidablePred P]
    (hN : ∀ k, k < m → b ≤ ∫ ω, N k ω ∂μ)
    (hzero : ∀ k, k < m → ¬ P k → ∫ ω, err k ω ∂μ ≤ 0)
    (hbd : ∀ k, k < m → ∫ ω, err k ω ∂μ ≤ ε) (hε : 0 ≤ ε)
    (hcard : ((range m).filter P).card ≤ F) :
    ∫ ω, D m ω ∂μ ≤ ∫ ω, D 0 ω ∂μ - κ * ((m : ℝ) * b) + (F : ℝ) * ε := by
  have hdrift : κ * ((m : ℝ) * b) ≤ ∑ k ∈ range m, κ * ∫ ω, N k ω ∂μ := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_ge_of_le hN) hκ
  have herr : ∑ k ∈ range m, ∫ ω, err k ω ∂μ ≤ (F : ℝ) * ε :=
    sum_err_le (P := P) hzero hbd hε hcard
  have := drift_bound h
  linarith

/-! ## 5. The parameters `T`, `N`, `h` and the budget

`T` is pinned from both sides (report §5 and hinge 1): `n²T/4 = 4 log n` is what Lemma 5.2 needs,
and `e^{n²T/8} = n²` is what Lemma 4.3 allows.  `numSteps` and `stepSize` are *free* — they appear
in no bound whose size matters — so the exponent `e` is chosen to make the discretisation error
negligible. -/

open Real

/-- `T = 16 log n / n²` (Klartag Lemma 5.2, p. 23). -/
noncomputable def horizon (n : ℕ) : ℝ := 16 * Real.log n / (n : ℝ) ^ 2

/-- `N = ⌈16 n^e log n⌉`: the number of steps.  Hinge 1 takes `e = 3`; the report recommends
`e = 5`. -/
noncomputable def numSteps (n e : ℕ) : ℕ := ⌈16 * (n : ℝ) ^ e * Real.log n⌉₊

/-- `h = T / N`, so that `N·h = T` exactly. -/
noncomputable def stepSize (n e : ℕ) : ℝ := horizon n / (numSteps n e : ℝ)

theorem log_pos_of_three {n : ℕ} (hn : 3 ≤ n) : 1 ≤ Real.log n := by
  have h3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have he : Real.exp 1 ≤ (n : ℝ) := le_trans (le_of_lt (by
    have := Real.exp_one_lt_d9
    linarith)) h3
  have := Real.log_le_log (Real.exp_pos 1) he
  rwa [Real.log_exp] at this

/-- **The pinned trade-off** `n²T/4 = 4 log n` (Klartag p. 23; report §5.1 item 2). -/
theorem tradeoff {n : ℕ} (hn : n ≠ 0) : (n : ℝ) ^ 2 * horizon n / 4 = 4 * Real.log n := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  rw [horizon]
  field_simp
  ring

theorem numSteps_pos {n e : ℕ} (hn : 3 ≤ n) : 0 < (numSteps n e : ℝ) := by
  have hlog := log_pos_of_three hn
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by
    have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hbase : (1 : ℝ) ≤ (n : ℝ) ^ e := one_le_pow₀ hn'
  have : (0 : ℝ) < 16 * (n : ℝ) ^ e * Real.log n := by nlinarith
  have hceil : 16 * (n : ℝ) ^ e * Real.log n ≤ (numSteps n e : ℝ) := Nat.le_ceil _
  linarith

/-- `h ≤ n^{-(e+2)}`: the step size the choice of `numSteps` delivers. -/
theorem stepSize_le {n e : ℕ} (hn : 3 ≤ n) : stepSize n e ≤ 1 / (n : ℝ) ^ (e + 2) := by
  have hlog := log_pos_of_three hn
  have hn' : (0 : ℝ) < (n : ℝ) := by
    have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hbase : (0 : ℝ) < (n : ℝ) ^ e := pow_pos hn' e
  have hden : (0 : ℝ) < 16 * (n : ℝ) ^ e * Real.log n := by nlinarith
  have hceil : 16 * (n : ℝ) ^ e * Real.log n ≤ (numSteps n e : ℝ) := Nat.le_ceil _
  have hT : (0 : ℝ) ≤ horizon n := by
    rw [horizon]; positivity
  calc stepSize n e = horizon n / (numSteps n e : ℝ) := rfl
    _ ≤ horizon n / (16 * (n : ℝ) ^ e * Real.log n) := by
        exact div_le_div_of_nonneg_left hT hden hceil
    _ = 1 / (n : ℝ) ^ (e + 2) := by
        rw [horizon, pow_add]
        field_simp

/-- **The discretisation-error budget.**  The total log-det cost of the freezes is at most
`d · sup overshoot ≤ n² · √(n h)` (report §5): at `e = 5` that is `≤ 1/n`, hence `o(1)`.
At hinge 1's `e = 3` the same expression is `1`, i.e. `O(1)` but **not** `o(1)`. -/
theorem proj_error_le {n e : ℕ} (hn : 3 ≤ n) (he : 5 ≤ e) :
    (n : ℝ) ^ 2 * Real.sqrt ((n : ℝ) * stepSize n e) ≤ 1 / (n : ℝ) := by
  have hn' : (0 : ℝ) < (n : ℝ) := by
    have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have h1 : (n : ℝ) * stepSize n e ≤ (n : ℝ) * (1 / (n : ℝ) ^ (e + 2)) :=
    mul_le_mul_of_nonneg_left (stepSize_le hn) hn'.le
  have h2 : (n : ℝ) * (1 / (n : ℝ) ^ (e + 2)) ≤ 1 / (n : ℝ) ^ 6 := by
    have hpow : (n : ℝ) ^ 7 ≤ (n : ℝ) ^ (e + 2) := by
      refine pow_le_pow_right₀ ?_ (by omega)
      have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    rw [mul_one_div]
    calc (n : ℝ) / (n : ℝ) ^ (e + 2) ≤ (n : ℝ) / (n : ℝ) ^ 7 :=
          div_le_div_of_nonneg_left hn'.le (by positivity) hpow
      _ = 1 / (n : ℝ) ^ 6 := by field_simp
  have h3 : Real.sqrt ((n : ℝ) * stepSize n e) ≤ 1 / (n : ℝ) ^ 3 := by
    have hsq : (1 : ℝ) / (n : ℝ) ^ 6 = (1 / (n : ℝ) ^ 3) ^ 2 := by
      rw [div_pow, one_pow, ← pow_mul]
    calc Real.sqrt ((n : ℝ) * stepSize n e) ≤ Real.sqrt (1 / (n : ℝ) ^ 6) :=
          Real.sqrt_le_sqrt (h1.trans h2)
      _ = 1 / (n : ℝ) ^ 3 := by rw [hsq, Real.sqrt_sq (by positivity)]
  calc (n : ℝ) ^ 2 * Real.sqrt ((n : ℝ) * stepSize n e)
      ≤ (n : ℝ) ^ 2 * (1 / (n : ℝ) ^ 3) := by
        exact mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = 1 / (n : ℝ) := by field_simp

end Submission.L10.ChainDrift

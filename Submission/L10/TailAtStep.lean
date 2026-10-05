/-
Gate L-10 (`klartag_packing`), brief 40.

**Proposition 4.1 at every step, and the Riemann comparison that feeds Lemma 4.3.**

Report 39 left one input open: `μ.real {ω | y ∈ C k ω} ≤ 4·profileAt … (k·h) ‖toE n y‖` for every
`k < N`.  `Padding.padded_tail_of_increments` is parameterised in the step count (`hitSet M N` is
the hitting event of the first `N` steps), so instantiating it at `N := k` is exactly Proposition
4.1 at horizon `k·h`; §1 turns its `Φ(M₀/(√t·q))` into `profileAt … t`.

**The `k = 0` term is load-bearing.**  `profile … 0 r = 1/2` on the whole window — `yOf a₀ 0 u` is
`(a₀ − u⁻²)/√0 = 0` in Lean and `PhiC 0 = 1/2` — so a Riemann sum that keeps `k = 0` adds a
constant `h/2` across the window, which is not radially integrable and would swamp Lemma 4.3's
shell term by `(W/ρ)ⁿ`.  It vanishes for the right reason: `hitSet M 0 = {M₀ ≤ 0}` is empty because
`padded_tail_of_increments`' own `hM₀ : 0 < M₀` says the point starts outside.  `profStep` records
that, and §2's comparison is stated for it.
-/
import Submission.L10.ContactIntegrated
import Submission.L10.ChainInputDom
import Submission.L10.ParamsAdopted2

namespace Submission.L10

open MeasureTheory Set Real Submission.L10.ChainDataInst Submission.L10.Tiling
open Submission.L10.Section5 Submission.L10.ConstructionA
open scoped ENNReal NNReal

/-! ## 1. Proposition 4.1 at step `k`, in the profile's language -/

/-- Klartag's tail argument is `yOf`: with `M₀ = a₀ − (α·r)⁻²` (eq. 61 at the scaled radius) and
`q = 1`, the argument of `Φ` in `padded_tail_of_increments` is `yOf a₀ t (α·r)`. -/
theorem tail_arg_eq (a₀ t u : ℝ) :
    (a₀ - (u ^ 2)⁻¹) / (Real.sqrt t * 1) = yOf a₀ t u := by
  unfold yOf; rw [mul_one]

/-- `padded_tail_of_increments`' variance hypothesis at step `k`: `k` increments of variance
`h·q²` make total variance `(k·h)·q²`. -/
theorem step_variance {δ : ℝ≥0} {hstep q : ℝ} (hδ : (δ : ℝ) = hstep * q ^ 2) (k : ℕ) :
    (((k • δ : ℝ≥0)) : ℝ) = ((k : ℝ) * hstep) * q ^ 2 := by
  have hc : ((k • δ : ℝ≥0) : ℝ) = (k : ℝ) * (δ : ℝ) := by simp [nsmul_eq_mul]
  rw [hc, hδ]; ring

/-- An `ℝ≥0∞` tail bound read as a real one. -/
theorem measureReal_le_of_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {s : Set Ω} {b : ℝ} (hb : 0 ≤ b)
    (h : μ s ≤ ENNReal.ofReal b) : μ.real s ≤ b := by
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rwa [ENNReal.toReal_ofReal hb] at this

/-- **Proposition 4.1 at step `k`, in the profile's language.**  From the `Φ` form of the padded
tail at horizon `k·h` to the `profileAt` form `ContactIntegrated.integrated_count_le` consumes. -/
theorem tail_at_step {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} {α hstep : ℝ} {N : ℕ} (C : ℕ → Ω → Finset (Fin n → ℤ))
    (W : Finset (Fin n → ℤ))
    (hwin : ∀ y ∈ W, ‖toE n y‖ + Real.sqrt n / 2 ≤ windowC α n)
    (hr : ∀ y ∈ W, 0 < α * ‖toE n y‖)
    (hy : ∀ k, k < N → k ≠ 0 → ∀ y ∈ W,
      0 < yOf (a0C n) ((k : ℝ) * hstep) (α * ‖toE n y‖))
    (hPhi : ∀ k, k < N → k ≠ 0 → ∀ y ∈ W,
      μ {ω | y ∈ C k ω}
        ≤ ENNReal.ofReal (4 * Phi (yOf (a0C n) ((k : ℝ) * hstep) (α * ‖toE n y‖))))
    (hzero : ∀ y ∈ W, μ.real {ω | y ∈ C 0 ω} = 0) :
    ∀ k, k < N → ∀ y ∈ W,
      μ.real {ω | y ∈ C k ω}
        ≤ 4 * (if k = 0 then 0 else
            profileAt (a0C n) α (windowC α n) n ((k : ℝ) * hstep) ‖toE n y‖) := by
  intro k hk y hy'
  by_cases hk0 : k = 0
  · subst hk0; rw [ite_eq_left rfl, mul_zero, hzero y hy']
  · rw [ite_eq_right hk0,
      profileAt_eq_Phi (hwin y hy') (hr y hy') (hy k hk hk0 y hy')]
    exact measureReal_le_of_le (by
      have := Phi_nonneg (hy k hk hk0 y hy'); linarith) (hPhi k hk hk0 y hy')

/-! ## 2. The Riemann comparison

`profile` is monotone in `t` (report 35), so the left-endpoint sum is **below** the integral — the
direction Lemma 4.3 needs.  The `k = 0` term is dropped, for the reason in the header. -/

/-- The per-step profile: Proposition 4.1's value at step time `k·h`, zero at `k = 0`. -/
noncomputable def profStep (α : ℝ) (n : ℕ) (hstep : ℝ) (y : Fin n → ℤ) (k : ℕ) : ℝ :=
  if k = 0 then 0 else profileAt (a0C n) α (windowC α n) n ((k : ℝ) * hstep) ‖toE n y‖

theorem riemann_lower_le {f : ℝ → ℝ} {hstep : ℝ} {N : ℕ} (hh : 0 < hstep)
    (hf0 : ∀ t, 0 ≤ f t)
    (hmono : ∀ s t : ℝ, 0 < s → s ≤ t → f s ≤ f t)
    (hint : ∀ b : ℝ, IntegrableOn f (Ioc (0 : ℝ) b)) :
    ∑ k ∈ Finset.range N, hstep * (if k = 0 then 0 else f ((k : ℝ) * hstep))
      ≤ ∫ t in Ioc (0 : ℝ) ((N : ℝ) * hstep), f t := by
  have hIOC : ∀ k : ℕ, IntegrableOn f (Ioc ((k : ℝ) * hstep) (((k : ℝ) + 1) * hstep)) := by
    intro k
    exact (hint (((k : ℝ) + 1) * hstep)).mono_set
      (Ioc_subset_Ioc_left (by positivity))
  have hadj : ∀ k ∈ Finset.range N,
      hstep * (if k = 0 then 0 else f ((k : ℝ) * hstep))
        ≤ ∫ t in Ioc ((k : ℝ) * hstep) (((k : ℝ) + 1) * hstep), f t := by
    intro k _
    by_cases hk : k = 0
    · subst hk
      rw [ite_eq_left rfl, mul_zero]
      exact setIntegral_nonneg measurableSet_Ioc (fun t _ => hf0 t)
    · rw [ite_eq_right hk]
      have hkpos : (0 : ℝ) < (k : ℝ) * hstep := by
        have hk1 : (0 : ℝ) < (k : ℝ) := by
          exact_mod_cast Nat.pos_of_ne_zero hk
        positivity
      have hconstint : IntegrableOn (fun _ : ℝ => f ((k : ℝ) * hstep))
          (Ioc ((k : ℝ) * hstep) (((k : ℝ) + 1) * hstep)) :=
        integrableOn_of_bounded' measurableSet_Ioc (by simp [Real.volume_Ioc])
          aestronglyMeasurable_const (M := ‖f ((k : ℝ) * hstep)‖) (fun _ _ => le_rfl)
      have hle := setIntegral_mono_on hconstint (hIOC k) measurableSet_Ioc
        (fun t ht => hmono _ _ hkpos ht.1.le)
      rwa [setIntegral_const, measureReal_def, Real.volume_Ioc,
        show ((k : ℝ) + 1) * hstep - (k : ℝ) * hstep = hstep by ring,
        ENNReal.toReal_ofReal hh.le, smul_eq_mul] at hle
  refine le_trans (Finset.sum_le_sum hadj) (le_of_eq ?_)
  have hcast : ∀ k : ℕ, ((k + 1 : ℕ) : ℝ) * hstep = ((k : ℝ) + 1) * hstep := by
    intro k; push_cast; ring
  have hII : ∀ k : ℕ, IntervalIntegrable f volume ((k : ℝ) * hstep) (((k : ℕ) + 1 : ℕ) * hstep) := by
    intro k
    rw [hcast k, intervalIntegrable_iff_integrableOn_Ioc_of_le (by nlinarith)]
    exact hIOC k
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k : ℕ => (k : ℝ) * hstep) (f := f) (μ := volume) (n := N)
    (fun k _ => hII k)
  have hrw : ∀ k : ℕ, (∫ t in ((k : ℝ) * hstep)..(((k + 1 : ℕ) : ℝ) * hstep), f t)
      = ∫ t in Ioc ((k : ℝ) * hstep) (((k : ℝ) + 1) * hstep), f t := by
    intro k
    rw [hcast k, intervalIntegral.integral_of_le (by nlinarith)]
  simp_rw [hrw] at hsum
  rw [hsum, Nat.cast_zero, zero_mul, intervalIntegral.integral_of_le (by positivity)]

/-! ## 3. `intWeight` is below Lemma 4.3's radial profile -/

theorem intWeight_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} {α hstep : ℝ} {N : ℕ} (_hα : 0 < α) (hh : 0 < hstep)
    (hNT : (N : ℝ) * hstep = ChainDrift.horizon n)
    (C : ℕ → Ω → Finset (Fin n → ℤ)) {y : Fin n → ℤ}
    (htail : ∀ k, k < N → μ.real {ω | y ∈ C k ω} ≤ 4 * profStep α n hstep y k) :
    ContactIntegrated.intWeight μ C hstep N y
      ≤ 4 * ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
          profileAt (a0C n) α (windowC α n) n t ‖toE n y‖ := by
  have hstep_le : ContactIntegrated.intWeight μ C hstep N y
      ≤ ∑ k ∈ Finset.range N, hstep * (4 * profStep α n hstep y k) := by
    rw [ContactIntegrated.intWeight]
    exact Finset.sum_le_sum (fun k hk =>
      mul_le_mul_of_nonneg_left (htail k (Finset.mem_range.1 hk)) hh.le)
  have hpull : ∑ k ∈ Finset.range N, hstep * (4 * profStep α n hstep y k)
      = 4 * ∑ k ∈ Finset.range N, hstep * profStep α n hstep y k := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun k _ => by ring)
  have hR := riemann_lower_le (f := fun t => profileAt (a0C n) α (windowC α n) n t ‖toE n y‖)
    (hstep := hstep) (N := N) hh
    (fun t => profile_nonneg _ _)
    (fun s t hs hst => profile_mono_time hs hst _)
    (fun b => integrableOn_profile_time (‖toE n y‖ + Real.sqrt n / 2))
  rw [hNT] at hR
  refine le_trans hstep_le ?_
  rw [hpull]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  simpa [profStep] using hR

/-! ## 4. The adopted discretisation

Report 39 wrote `stepSize n 5` / `numSteps n 5`, which are what `ChainDataInst.Params.N_eq` and
`h_eq` pin.  The chain is actually run at `ParamsAdopted2`'s successors, `e = 7`
(`h ≤ n⁻⁹`, `N = ⌈16 n⁷ log n⌉`).  **`e = 7` is what `intWeight` uses here**, and that is
consistent: `Params.N` and `Params.h` are inert — `Params`' own docstring records that §5 "does not
use `T`, `N`, `h` at all", and nothing in Lemma 4.3 reads them either; only `N·h = T` matters, and
that holds for every `e`. -/

theorem adopted_horizon {n : ℕ} (hn : 3 ≤ n) :
    (ParamsAdopted2.numStepsAdopted2 n : ℝ) * ParamsAdopted2.stepSizeAdopted2 n
      = ChainDrift.horizon n :=
  ParamsAdopted2.numStepsAdopted2_mul_stepSizeAdopted2 hn

theorem horizon_pos {n : ℕ} (hn : 3 ≤ n) : 0 < ChainDrift.horizon n := by
  have hlog : (1 : ℝ) ≤ Real.log n := ChainDrift.log_pos_of_three hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  rw [ChainDrift.horizon]
  exact div_pos (by linarith) (by positivity)

theorem adopted_stepSize_pos {n : ℕ} (hn : 3 ≤ n) : 0 < ParamsAdopted2.stepSizeAdopted2 n := by
  rw [ParamsAdopted2.stepSizeAdopted2, ChainDrift.stepSize]
  exact div_pos (horizon_pos hn) (ChainDrift.numSteps_pos hn)

/-- **`ChainRaw2.tail`, discharged.**  The per-step tail of §1, summed by §2 and §3, at the
adopted `e = 7` discretisation. -/
theorem tail_of_steps {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} {α : ℝ} (hn : 3 ≤ n) (hα : 0 < α) (C : ℕ → Ω → Finset (Fin n → ℤ))
    {y : Fin n → ℤ}
    (hsteps : ∀ k, k < ParamsAdopted2.numStepsAdopted2 n →
      μ.real {ω | y ∈ C k ω}
        ≤ 4 * profStep α n (ParamsAdopted2.stepSizeAdopted2 n) y k) :
    ENNReal.ofReal (ContactIntegrated.intWeight μ C
        (ParamsAdopted2.stepSizeAdopted2 n) (ParamsAdopted2.numStepsAdopted2 n) y)
      ≤ ENNReal.ofReal (4 * ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
          profileAt (a0C n) α (windowC α n) n t ‖toE n y‖) :=
  ENNReal.ofReal_le_ofReal
    (intWeight_le hα (adopted_stepSize_pos hn) (adopted_horizon hn) C hsteps)

/-! ## 5. `ChainRaw2` — the factor 4 in the weight, and Lemma 4.3's hand-off -/

/-- `ChainRaw` with the `4` of `padded_tail_of_increments` carried in `tail` (report 39 §3: the
factor goes into `f`, never into `alpha`, which `alpha_norm` pins). -/
structure ChainRaw2 (p n : ℕ) where
  alpha : ℝ
  alpha_pos : 0 < alpha
  alpha_norm : alpha ^ n * ((p ^ (n - 1) : ℕ) : ℝ) = kappa n
  R : ℝ
  R_nonneg : 0 ≤ R
  R_scaled : alpha * R ≤ 1 - 1 / (n : ℝ)
  R_lt_p : R < (p : ℝ)
  tiling_defect : (n : ℝ) * (alpha * Real.sqrt n / 2) ≤ 1 / 4
  window_lt_p : windowC alpha n < (p : ℝ)
  w : (Fin n → ℤ) → ℝ≥0∞
  supp : Finset (Fin n → ℤ)
  supp_ne_zero : ∀ y ∈ supp, y ≠ 0
  supp_radius : ∀ y ∈ supp, ‖toE n y‖ ≤ windowC alpha n
  /-- The only probabilistic input; `tail_of_steps` supplies it. -/
  tail : ∀ y ∈ supp, w y ≤ ENNReal.ofReal
    (4 * ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
      profileAt (a0C n) alpha (windowC alpha n) n t ‖toE n y‖)
  arith : (n : ℝ) * kappa n * ((p : ℝ) - 1) * (8 - 8 / (n : ℝ) ^ 2) < 8 * ((p : ℝ) ^ n - 1)

/-- Lemma 4.3's profile with the factor 4. -/
noncomputable def fC4 (α : ℝ) (n : ℕ) : ℝ → ℝ := fun r => 4 * fC α n r

/-- **`Params.dom` against `c · profile`.**  `dom_of_tail` rescaled; `c ≥ 0` is all that is used. -/
theorem dom_of_tail2 {n : ℕ} (hn : 0 < n) {a₀ α W T c : ℝ} (hα : 0 < α) (hc : 0 ≤ c)
    (w : (Fin n → ℤ) → ℝ≥0∞) (supp : Finset (Fin n → ℤ))
    (htail : ∀ y ∈ supp, w y ≤ ENNReal.ofReal
      (c * ∫ t in Ioc (0 : ℝ) T, profileAt a₀ α W n t ‖toE n y‖)) :
    ∀ y ∈ supp, ∀ x ∈ cube (toE n y),
      w y ≤ ENNReal.ofReal (c * ∫ t in Ioc (0 : ℝ) T, profile a₀ α W n t ‖x‖) := by
  intro y hy x hx
  have hbase : Antitone (fun r : ℝ => ∫ t in Ioc (0 : ℝ) T, profileAt a₀ α W n t r) :=
    antitone_integral (fun t ht => profileAt_antitone hα ht.1)
      (fun r => integrableOn_profile_time (r + Real.sqrt n / 2))
  have hanti : Antitone (fun r : ℝ => c * ∫ t in Ioc (0 : ℝ) T, profileAt a₀ α W n t r) :=
    fun _ _ h => mul_le_mul_of_nonneg_left (hbase h) hc
  have hwide := dom_of_antitone hn hanti supp y hy x hx
  have heq : (c * ∫ t in Ioc (0 : ℝ) T, profileAt a₀ α W n t (‖x‖ - Real.sqrt n / 2))
      = c * ∫ t in Ioc (0 : ℝ) T, profile a₀ α W n t ‖x‖ := by
    simp [profileAt, sub_add_cancel]
  rw [heq] at hwide
  exact le_trans (htail y hy) hwide

/-- **`Params` from `ChainRaw2`** — every field supplied, with `f = 4·profile`. -/
noncomputable def params_of_raw2 {p n : ℕ} [Fact (Nat.Prime p)] (hn : 2073600 ≤ n)
    (Q : ChainRaw2 p n) : Params p n where
  dim_pos := by omega
  alpha := Q.alpha
  alpha_pos := Q.alpha_pos
  alpha_norm := Q.alpha_norm
  a0 := a0C n
  a0_eq := rfl
  R := Q.R
  R_nonneg := Q.R_nonneg
  R_scaled := Q.R_scaled
  R_lt_p := Q.R_lt_p
  tiling_defect := Q.tiling_defect
  T := ChainDrift.horizon n
  T_eq := rfl
  N := ChainDrift.numSteps n 5
  N_eq := rfl
  h := ChainDrift.stepSize n 5
  h_eq := rfl
  windowRadius := windowC Q.alpha n
  window_lt_p := Q.window_lt_p
  f := fC4 Q.alpha n
  f_nonneg := fun r => by
    have h : (0 : ℝ) ≤ ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
        profile (a0C n) Q.alpha (windowC Q.alpha n) n t r :=
      setIntegral_nonneg measurableSet_Ioc (fun t _ => profile_nonneg t r)
    unfold fC4 fC
    linarith
  w := Q.w
  supp := Q.supp
  supp_ne_zero := Q.supp_ne_zero
  supp_radius := Q.supp_radius
  dom := dom_of_tail2 (by omega) Q.alpha_pos (by norm_num) Q.w Q.supp Q.tail
  integrable := by
    have h := integrable_radial_euclidean (a₀ := a0C n) (α := Q.alpha)
      (W := windowC Q.alpha n) (T := ChainDrift.horizon n) (n := n)
      (T_nonneg (by omega : 1 ≤ n))
    exact h.const_mul 4
  C := 4 * C1C Q.alpha n * (8 - 8 / (n : ℝ) ^ 2)
  radial_bound := by
    have h := radial_bound_of_chain (a₀ := a0C n) (α := Q.alpha)
      (W := windowC Q.alpha n) (T := ChainDrift.horizon n) (n := n)
      hn Q.alpha_pos (a0C_ge_one (by omega)) (a0C_le_four (by omega))
      Q.tiling_defect (horizon_eq n) rfl
    have heq : ∀ y : ℝ, y ^ (n - 1) * fC4 Q.alpha n y = 4 * (y ^ (n - 1) * fC Q.alpha n y) := by
      intro y; unfold fC4; ring
    rw [setIntegral_congr_fun measurableSet_Ioi (fun y _ => heq y),
      MeasureTheory.integral_const_mul]
    have h4 := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 4)
    simp only [C1C, fC]
    linarith
  theta := ENNReal.ofReal (16 * (4 * C1C Q.alpha n))
  theta_ne_zero := by
    have := C1C_pos (α := Q.alpha) (n := n) (by omega) Q.alpha_pos
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    linarith
  theta_ne_top := ENNReal.ofReal_ne_top
  markov :=
    markov_of_arith (by omega) (Nat.Prime.one_lt (Fact.out)).le
      (Nat.one_lt_pow (by omega) (Nat.Prime.one_lt (Fact.out)))
      (by have := C1C_pos (α := Q.alpha) (n := n) (by omega) Q.alpha_pos; linarith) Q.arith

/-- **The hand-off.**  `Threshold2.remaining_of_lemma43` fed from `ChainRaw2` alone. -/
theorem lemma43_input_of_raw2 {c₀ : ℝ} (hc₀ : 0 < c₀)
    (H : ∀ m : ℕ, Threshold2.n₁ ≤ m →
      ∃ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p) (Q : ChainRaw2 p (m + 1)),
        ∀ g : Fin (m + 1) → ZMod p, g ≠ 0 →
          (∀ y : Fin (m + 1) → ℤ, y ≠ 0 → ‖toE (m + 1) y‖ ≤ Q.R → y ∉ latZ p (m + 1) g) →
          Assembly.ChainOutput Q.alpha g c₀) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      let V := EuclideanSpace ℝ (Fin (n + 1))
      ∃ φ : V →ₗ[ℝ] V, let E := φ '' Metric.ball (0 : V) 1
        (MeasureTheory.volume E : EReal) = c * n ^ 2 ∧
        {v ∈ E | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} :=
  Threshold2.remaining_of_lemma43 hc₀ (fun m hm => by
    have hm' : 2073600 ≤ m := by simpa [Threshold2.n₁] using hm
    obtain ⟨p, hp, hp0, Q, h⟩ := H m hm'
    exact ⟨p, hp, hp0, params_of_raw2 (by omega) Q, h⟩)

/-! ## 6. `ChainRaw2` from the chain -/

/-- **`ChainRaw2` from the chain's definitions**, with `w = intWeight` and `tail` discharged by
`tail_of_steps`.  The thirteen remaining arguments are the chain's own lattice data and §5
arithmetic; the only probabilistic input is `hsteps`, Proposition 4.1 at every step. -/
noncomputable def chainRaw2_of_chain {p n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (hn : 3 ≤ n)
    (C : ℕ → Ω → Finset (Fin n → ℤ))
    (alpha : ℝ) (alpha_pos : 0 < alpha)
    (alpha_norm : alpha ^ n * ((p ^ (n - 1) : ℕ) : ℝ) = kappa n)
    (R : ℝ) (R_nonneg : 0 ≤ R) (R_scaled : alpha * R ≤ 1 - 1 / (n : ℝ)) (R_lt_p : R < (p : ℝ))
    (tiling_defect : (n : ℝ) * (alpha * Real.sqrt n / 2) ≤ 1 / 4)
    (window_lt_p : windowC alpha n < (p : ℝ))
    (supp : Finset (Fin n → ℤ)) (supp_ne_zero : ∀ y ∈ supp, y ≠ 0)
    (supp_radius : ∀ y ∈ supp, ‖toE n y‖ ≤ windowC alpha n)
    (hsteps : ∀ y ∈ supp, ∀ k, k < ParamsAdopted2.numStepsAdopted2 n →
      μ.real {ω | y ∈ C k ω}
        ≤ 4 * profStep alpha n (ParamsAdopted2.stepSizeAdopted2 n) y k)
    (arith : (n : ℝ) * kappa n * ((p : ℝ) - 1) * (8 - 8 / (n : ℝ) ^ 2) < 8 * ((p : ℝ) ^ n - 1)) :
    ChainRaw2 p n where
  alpha := alpha
  alpha_pos := alpha_pos
  alpha_norm := alpha_norm
  R := R
  R_nonneg := R_nonneg
  R_scaled := R_scaled
  R_lt_p := R_lt_p
  tiling_defect := tiling_defect
  window_lt_p := window_lt_p
  w := fun y => ENNReal.ofReal (ContactIntegrated.intWeight μ C
    (ParamsAdopted2.stepSizeAdopted2 n) (ParamsAdopted2.numStepsAdopted2 n) y)
  supp := supp
  supp_ne_zero := supp_ne_zero
  supp_radius := supp_radius
  tail := fun y hy => tail_of_steps hn alpha_pos C (hsteps y hy)
  arith := arith

end Submission.L10

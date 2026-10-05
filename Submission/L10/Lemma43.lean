/-
Gate L-10 (`klartag_packing`), brief 9.

**Lemma 4.3's radial integral and the load-bearing `1/8`** (Klartag, arXiv:2504.05042, p. 19-21).

The lemma bounds the integral of the contact weight over the spherical shell `R_t` by
`C · e^{n²t/8} · Vol(Bⁿ)`.  The `1/8` in that exponent is **not a constant with slack**: it is the
exponent that *is* the `n²` of Theorem 1.2.  Report 9 §1 works the arithmetic; in one line, the two
constraints

  `n²T/4 = 4 log n`   (Prop 3.4 / Lemma 5.2)   and   `γ n²T ≤ 2 log n`   (`∫₀^T K_t dt = O(1)`)

force `Vol ≳ c·n^{1/(4γ)}` for an exponent constant `γ`, so `γ ≤ 1/8` is necessary and `γ = 1/8`
gives `n²` on the nose.  A crude `-log(1-x) ≤ 2x` in place of the sharp `-log(1-x) ≤ x + x²` gives
`γ = 1/2` and a theorem about `n^{1/2}`.

This module proves the sharp bound and carries it to the pointwise integrand estimate in which the
`1/8` appears explicitly, then the radial (`∫⁻`) reduction that `Section5.weight_bound_of_lintegral`
consumes.  Nothing here is asymptotic: every constant is a named hypothesis, so there is no `n₀`.

**Where the `1/8` comes from, in three steps.**
1. `(1 - y√t)^{-(n+2)/2} ≤ exp(((n+2)/2)(y√t + y²t))`  — the *sharp* log bound.
2. `Φ(y) ≤ e^{-y²/2}/(√(2π)·y)`  — `PaddedTail.Phi`, the `1/r` tail of report 2.
3. `-y²/2 + b·y = -(y-b)²/2 + b²/2` with `b = n√t/2`, so `b²/2 = n²t/8`.

Step 3 is the whole of it: the `1/8` is the Legendre value of the Gaussian exponent at drift
`n√t/2`, and the drift is `n√t/2` rather than `n√t` exactly because step 1 is sharp.
-/
import Submission.L10.PaddedTail
import Submission.L10.Section5

namespace Submission.L10

open MeasureTheory Set Real
open scoped ENNReal NNReal

/-! ## 1. The sharp logarithm bound -/

/-- **The sharp bound.**  `-log(1-x) ≤ x + x²` for `0 ≤ x ≤ 1/2`.

This is the step that fixes the `1/8`.  The crude `-log(1-x) ≤ 2x`, also true on `[0,1/2]`, would
put `γ = 1/2` and destroy the `n²`. -/
theorem neg_log_one_sub_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    -Real.log (1 - x) ≤ x + x ^ 2 := by
  have hle : ∀ z : ℝ, z ∈ Set.Icc (0 : ℝ) (1 / 2) →
      0 ≤ Real.log (1 - z) + z + z ^ 2 := by
    set f : ℝ → ℝ := fun z => Real.log (1 - z) + z + z ^ 2 with hfdef
    set g : ℝ → ℝ := fun z => z * (1 - 2 * z) / (1 - z) with hgdef
    have hderiv : ∀ z : ℝ, z < 1 → HasDerivAt f (g z) z := by
      intro z hz
      have h1z : (1 : ℝ) - z ≠ 0 := by linarith
      have hlin : HasDerivAt (fun y : ℝ => 1 - y) (-1) z := by
        simpa using (hasDerivAt_id z).const_sub 1
      have hlog : HasDerivAt (fun y : ℝ => Real.log (1 - y)) ((1 - z)⁻¹ * (-1)) z :=
        (Real.hasDerivAt_log h1z).comp z hlin
      have hid : HasDerivAt (fun y : ℝ => y) 1 z := hasDerivAt_id z
      have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * z) z := by
        simpa using (hasDerivAt_pow 2 z)
      have hsum : HasDerivAt f ((1 - z)⁻¹ * (-1) + 1 + 2 * z) z := (hlog.add hid).add hsq
      have heq : (1 - z)⁻¹ * (-1) + 1 + 2 * z = g z := by
        rw [hgdef]; field_simp; ring
      rwa [heq] at hsum
    have hcont : ContinuousOn f (Set.Icc (0 : ℝ) (1 / 2)) := by
      refine ContinuousOn.add (ContinuousOn.add ?_ continuousOn_id) (by fun_prop)
      refine Real.continuousOn_log.comp (by fun_prop) ?_
      intro z hz
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      have := hz.2
      intro hcon
      simp only [sub_eq_zero] at hcon
      linarith [hz.2, hcon]
    have hmono : MonotoneOn f (Set.Icc (0 : ℝ) (1 / 2)) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := g) (convex_Icc 0 (1 / 2)) hcont
      · intro z hz
        rw [interior_Icc] at hz
        exact (hderiv z (by linarith [hz.2])).hasDerivWithinAt
      · intro z hz
        rw [interior_Icc] at hz
        rw [hgdef]
        refine div_nonneg (mul_nonneg (le_of_lt hz.1) (by linarith [hz.2])) (by linarith [hz.2])
    intro z hz
    have hf0 : f 0 = 0 := by simp [hfdef]
    have := hmono (Set.left_mem_Icc.2 (by norm_num)) hz hz.1
    have hfz : f z = Real.log (1 - z) + z + z ^ 2 := rfl
    linarith [this, hf0.ge, hf0.le, hfz.ge, hfz.le]
  have := hle x ⟨hx0, hx⟩
  linarith

/-- The crude bound, for the comparison in the report: `-log(1-x) ≤ 2x` on `[0,1/2]`.  True, and
four times too weak in the exponent. -/
theorem neg_log_one_sub_le_crude {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    -Real.log (1 - x) ≤ 2 * x := by
  have h := neg_log_one_sub_le hx0 hx
  nlinarith [sq_nonneg x]

/-! ## 2. The `rpow` form -/

/-- `(1 - x)^{-m/2} ≤ exp((m/2)·(x + x²))` for `0 ≤ x ≤ 1/2` and `0 ≤ m`. -/
theorem rpow_one_sub_le_exp {x m : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (hm : 0 ≤ m) :
    (1 - x) ^ (-(m / 2)) ≤ Real.exp (m / 2 * (x + x ^ 2)) := by
  have hpos : (0 : ℝ) < 1 - x := by linarith
  rw [Real.rpow_def_of_pos hpos]
  refine Real.exp_le_exp.2 ?_
  have h := neg_log_one_sub_le hx0 hx
  nlinarith [h, hm]

/-! ## 3. Completing the square — the `1/8` -/

/-- `-y²/2 + b·y = -(y-b)²/2 + b²/2`. -/
theorem neg_sq_half_add_mul (y b : ℝ) :
    -y ^ 2 / 2 + b * y = -(y - b) ^ 2 / 2 + b ^ 2 / 2 := by ring

/-- **The `1/8`.**  With drift `b = n√t/2`, the Legendre value is `b²/2 = n²t/8`. -/
theorem half_sq_drift (n : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    (n * Real.sqrt t / 2) ^ 2 / 2 = n ^ 2 * t / 8 := by
  have hs : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht
  field_simp
  nlinarith [hs]

/-- The crude bound's value, for the comparison: drift `n√t` gives `n²t/2`, four times larger. -/
theorem half_sq_drift_crude (n : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    (n * Real.sqrt t) ^ 2 / 2 = n ^ 2 * t / 2 := by
  have hs : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht
  nlinarith [hs]

/-! ## 4. The pointwise integrand bound -/

/-- **Lemma 4.3's integrand, bounded, with the `1/8` explicit.**

For `y > 0` with `y√t ≤ 1/2`,

  `Φ(y)·(1 - y√t)^{-(n+2)/2} ≤ (e^J / (√(2π)·y)) · e^{n²t/8} · e^{-(y - n√t/2)²/2}`

where `J` bounds the junk `y√t + ((n+2)/2)·(y√t)²`.  On the paper's range
(`1 ≤ y ≤ log n`, `√t ≤ 5√(log n)/n`) the junk is `o(1)`, so `J` may be taken to be any fixed
positive number for `n` past a threshold — but nothing here needs that: `J` is a hypothesis, so the
statement has no `n₀`.

The three ingredients are `PaddedTail.Phi`'s `1/r` branch, `rpow_one_sub_le_exp` (the sharp log
bound), and `neg_sq_half_add_mul` + `half_sq_drift` (completing the square). -/
theorem integrand_le {n : ℕ} {t y J : ℝ} (ht : 0 ≤ t) (hy : 0 < y)
    (hys : y * Real.sqrt t ≤ 1 / 2)
    (hJ : y * Real.sqrt t + ((n : ℝ) + 2) / 2 * (y * Real.sqrt t) ^ 2 ≤ J) :
    Phi y * (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2))
      ≤ Real.exp J / (Real.sqrt (2 * π) * y)
        * Real.exp ((n : ℝ) ^ 2 * t / 8)
        * Real.exp (-(y - (n : ℝ) * Real.sqrt t / 2) ^ 2 / 2) := by
  have hs0 : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hys0 : 0 ≤ y * Real.sqrt t := mul_nonneg hy.le hs0
  have hm : (0 : ℝ) ≤ (n : ℝ) + 2 := by positivity
  -- the `Φ` factor
  have hPhi : Phi y ≤ Real.exp (-y ^ 2 / 2) / (Real.sqrt (2 * π) * y) := by
    have h := min_le_right (1 / 2 : ℝ) (Real.exp (-y ^ 2 / 2) / (Real.sqrt (2 * π) * y))
    exact h
  have hPhi0 : 0 ≤ Phi y := Phi_nonneg hy
  -- the `rpow` factor
  have hrp : (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2))
      ≤ Real.exp (((n : ℝ) + 2) / 2 * (y * Real.sqrt t + (y * Real.sqrt t) ^ 2)) :=
    rpow_one_sub_le_exp hys0 hys hm
  have hrp0 : (0 : ℝ) < (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2)) :=
    Real.rpow_pos_of_pos (by linarith) _
  have hsy : (0 : ℝ) < Real.sqrt (2 * π) * y :=
    mul_pos (Real.sqrt_pos.2 (by positivity)) hy
  -- multiply the two bounds
  have hmul : Phi y * (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2))
      ≤ (Real.exp (-y ^ 2 / 2) / (Real.sqrt (2 * π) * y))
        * Real.exp (((n : ℝ) + 2) / 2 * (y * Real.sqrt t + (y * Real.sqrt t) ^ 2)) := by
    refine mul_le_mul hPhi hrp hrp0.le (by positivity)
  refine le_trans hmul ?_
  -- now it is one inequality between exponentials
  have hexp : Real.exp (-y ^ 2 / 2)
        * Real.exp (((n : ℝ) + 2) / 2 * (y * Real.sqrt t + (y * Real.sqrt t) ^ 2))
      ≤ Real.exp J * (Real.exp ((n : ℝ) ^ 2 * t / 8)
        * Real.exp (-(y - (n : ℝ) * Real.sqrt t / 2) ^ 2 / 2)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have hb : -y ^ 2 / 2 + ((n : ℝ) * Real.sqrt t / 2) * y
        = -(y - (n : ℝ) * Real.sqrt t / 2) ^ 2 / 2 + ((n : ℝ) * Real.sqrt t / 2) ^ 2 / 2 :=
      neg_sq_half_add_mul y _
    have hd : ((n : ℝ) * Real.sqrt t / 2) ^ 2 / 2 = (n : ℝ) ^ 2 * t / 8 := half_sq_drift _ ht
    have hsplit : ((n : ℝ) + 2) / 2 * (y * Real.sqrt t + (y * Real.sqrt t) ^ 2)
        = ((n : ℝ) * Real.sqrt t / 2) * y
          + (y * Real.sqrt t + ((n : ℝ) + 2) / 2 * (y * Real.sqrt t) ^ 2) := by
      ring
    rw [hsplit, ← add_assoc, hb, hd]
    linarith [hJ]
  calc (Real.exp (-y ^ 2 / 2) / (Real.sqrt (2 * π) * y))
        * Real.exp (((n : ℝ) + 2) / 2 * (y * Real.sqrt t + (y * Real.sqrt t) ^ 2))
      = (Real.exp (-y ^ 2 / 2)
          * Real.exp (((n : ℝ) + 2) / 2 * (y * Real.sqrt t + (y * Real.sqrt t) ^ 2)))
        / (Real.sqrt (2 * π) * y) := by ring
    _ ≤ (Real.exp J * (Real.exp ((n : ℝ) ^ 2 * t / 8)
          * Real.exp (-(y - (n : ℝ) * Real.sqrt t / 2) ^ 2 / 2))) / (Real.sqrt (2 * π) * y) := by
        exact div_le_div_of_nonneg_right hexp hsy.le
    _ = Real.exp J / (Real.sqrt (2 * π) * y) * Real.exp ((n : ℝ) ^ 2 * t / 8)
          * Real.exp (-(y - (n : ℝ) * Real.sqrt t / 2) ^ 2 / 2) := by ring

/-! ## 5. The two elementary constants of the `I₁` and `I₃` pieces

Klartag's `I₁` and `I₃` are absorbed by `e^x ≤ C·x⁻¹·e^{x²/8}` and `c ≤ x⁻¹·e^{x²/8}` (p. 20,
eqs. 57-58).  Both are one completed square.  The constants are *not* load-bearing — only the `1/8`
in the exponent is — so the cheap `log x ≤ x - 1` route is taken, giving `e^7` where the sharp
constant is `e^{3.49}`. -/

/-- `x·e^{x - x²/8} ≤ e^7` for `x > 0`, i.e. `e^x ≤ (e^7/x)·e^{x²/8}`.  This is eq. (57)'s
absorption; `(x-8)² ≥ 0` is the whole proof. -/
theorem mul_exp_sub_sq_le {x : ℝ} (hx : 0 < x) :
    x * Real.exp (x - x ^ 2 / 8) ≤ Real.exp 7 := by
  have hlog : Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos hx
  have hkey : Real.log x + (x - x ^ 2 / 8) ≤ 7 := by nlinarith [sq_nonneg (x - 8)]
  calc x * Real.exp (x - x ^ 2 / 8)
      = Real.exp (Real.log x) * Real.exp (x - x ^ 2 / 8) := by rw [Real.exp_log hx]
    _ = Real.exp (Real.log x + (x - x ^ 2 / 8)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp 7 := Real.exp_le_exp.2 hkey

/-- `x⁻¹·e^{x²/8} ≥ 1/√2` for `x > 0`.  This is eq. (58)'s absorption; `(x - 2√2)² ≥ 0` is the
whole proof. -/
theorem inv_mul_exp_sq_ge {x : ℝ} (hx : 0 < x) :
    1 / Real.sqrt 2 ≤ Real.exp (x ^ 2 / 8) / x := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hexp : 1 + x ^ 2 / 8 ≤ Real.exp (x ^ 2 / 8) := by
    have := Real.add_one_le_exp (x ^ 2 / 8)
    linarith
  have hkey : 1 / Real.sqrt 2 ≤ (1 + x ^ 2 / 8) / x := by
    rw [le_div_iff₀ hx]
    have h2 : 1 / Real.sqrt 2 * x = x / Real.sqrt 2 := by ring
    rw [h2, div_le_iff₀ hs0]
    nlinarith [sq_nonneg (x - 2 * Real.sqrt 2), hs, hs0]
  refine le_trans hkey ?_
  exact div_le_div_of_nonneg_right hexp hx.le

/-! ## 6. The radial reduction — `∫⁻` from `integral_fun_norm_addHaar`

Report 5 §4.1 flagged that `MeasureTheory.integral_fun_norm_addHaar` is a **Bochner** integral and
that there is no `lintegral` variant at the pin.  The bridge is
`MeasureTheory.ofReal_integral_eq_lintegral_ofReal`, which needs integrability — the hypothesis
`hint` below.  For the chain's weight `ψ` that is easy: it is bounded (by `Φ ≤ 1/2`) and supported
on the bounded shell `R_t`. -/

open Submission.L10.Section5 in
/-- **The radial reduction.**  For a non-negative radial integrand,
`∫⁻ x, ofReal (f ‖x‖) ≤ ofReal (n · κ_n · C)` whenever the one-dimensional integral is `≤ C`. -/
theorem lintegral_radial_le {n : ℕ} (hn : 0 < n) {f : ℝ → ℝ}
    (hf0 : ∀ r : ℝ, 0 ≤ f r)
    (hint : Integrable (fun x : EuclideanSpace ℝ (Fin n) => f ‖x‖))
    {C : ℝ} (hC : ∫ y in Ioi (0 : ℝ), y ^ (n - 1) * f y ≤ C) :
    ∫⁻ x : EuclideanSpace ℝ (Fin n), ENNReal.ofReal (f ‖x‖)
      ≤ ENNReal.ofReal ((n : ℝ) * kappa n * C) := by
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; exact hn)
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
  have hpolar := MeasureTheory.integral_fun_norm_addHaar
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) f
  rw [hdim] at hpolar
  have hmeas : (volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball 0 1) = kappa n := rfl
  rw [hmeas] at hpolar
  simp only [nsmul_eq_mul, smul_eq_mul] at hpolar
  have hbridge : ENNReal.ofReal (∫ x : EuclideanSpace ℝ (Fin n), f ‖x‖)
      = ∫⁻ x : EuclideanSpace ℝ (Fin n), ENNReal.ofReal (f ‖x‖) :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall (fun x => hf0 _))
  rw [← hbridge, hpolar]
  refine ENNReal.ofReal_le_ofReal ?_
  have hk : 0 ≤ (n : ℝ) * kappa n := by
    have := kappa_nonneg n
    positivity
  calc (n : ℝ) * (kappa n * ∫ y in Ioi (0 : ℝ), y ^ (n - 1) * f y)
      = (n : ℝ) * kappa n * ∫ y in Ioi (0 : ℝ), y ^ (n - 1) * f y := by ring
    _ ≤ (n : ℝ) * kappa n * C := by exact mul_le_mul_of_nonneg_left hC hk

/-! ## 7. The statement `ChainData` consumes

`Section5.weight_bound_of_lintegral` takes a general `ψ` and a number `I`.  This specialises it to
a **radial** `ψ` and supplies `I` from the one-dimensional bound, which is exactly the shape
Lemma 4.3 produces.  `ChainData.weight_bound` is then discharged by applying this with
`C = C₁ · e^{n²T/8} / n` and `theta` Klartag's Markov threshold. -/

open Submission.L10.Section5 in
/-- **`ChainData.weight_bound` from a radial one-dimensional bound.**

This is the exact statement the interface consumes: give a non-negative radial profile `f`
dominating the contact weight on each unit cube, an integrability certificate, and a bound `C` on
`∫₀^∞ yⁿ⁻¹ f(y) dy`; the Markov threshold field follows. -/
theorem weight_bound_of_radial {p n : ℕ} [Fact (Nat.Prime p)] (hn : 0 < n)
    (B : Finset (Fin n → ℤ))
    (w : (Fin n → ℤ) → ℝ≥0∞) (f : ℝ → ℝ) (hf0 : ∀ r : ℝ, 0 ≤ f r)
    (hdom : ∀ y ∈ B, ∀ x ∈ Tiling.cube (Tiling.toE n y), w y ≤ ENNReal.ofReal (f ‖x‖))
    (hint : Integrable (fun x : EuclideanSpace ℝ (Fin n) => f ‖x‖))
    {C : ℝ} (hC : ∫ y in Ioi (0 : ℝ), y ^ (n - 1) * f y ≤ C)
    (θ : ℝ≥0∞)
    (hnum : 2 * (((p - 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal ((n : ℝ) * kappa n * C))
        < θ * ((p ^ n - 1 : ℕ) : ℝ≥0∞)) :
    2 * (((p - 1 : ℕ) : ℝ≥0∞) * ∑ y ∈ B, w y) < θ * ((p ^ n - 1 : ℕ) : ℝ≥0∞) :=
  weight_bound_of_lintegral B w (fun x => ENNReal.ofReal (f ‖x‖)) hdom θ
    (ENNReal.ofReal ((n : ℝ) * kappa n * C)) (lintegral_radial_le hn hf0 hint hC) hnum

/-! ## 8. The one-dimensional estimate, reduced to one Gaussian integral

Klartag's `I₂` (p. 20-21, eqs. 59) is the only piece of the three-way split that is not elementary
arithmetic.  `integrand_le` factors `e^{n²t/8}` out of it exactly, leaving

  `∫₁^L e^{-(y-b)²/2}/y dy`,   `b = n√t/2`,

a pure Gaussian integral with no `n` and no `t` in it beyond `b`.  `oneDim_le` is that reduction;
`prefactor_cancel` is the arithmetic that turns the paper's `K ≤ (2 + 2√(2π))/b` into an absolute
constant once the prefactor `n√t/2 = b` of eq. (56) is restored.  Together they say: **the `1/8` is
the entire `n`-dependence of `I₂`.** -/

/-- **`I₂` with `e^{n²t/8}` factored out.**  The remaining integral is Gaussian. -/
theorem oneDim_le {n : ℕ} {t J K L : ℝ} (ht : 0 ≤ t)
    (hLs : L * Real.sqrt t ≤ 1 / 2)
    (hJ : ∀ y ∈ Ioc (1 : ℝ) L,
      y * Real.sqrt t + ((n : ℝ) + 2) / 2 * (y * Real.sqrt t) ^ 2 ≤ J)
    (hint1 : IntegrableOn
      (fun y : ℝ => Phi y * (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2))) (Ioc 1 L))
    (hint2 : IntegrableOn (fun y : ℝ =>
      Real.exp J / Real.sqrt (2 * π) * Real.exp ((n : ℝ) ^ 2 * t / 8)
        * (Real.exp (-(y - (n : ℝ) * Real.sqrt t / 2) ^ 2 / 2) / y)) (Ioc 1 L))
    (hK : ∫ y in Ioc (1 : ℝ) L,
      Real.exp (-(y - (n : ℝ) * Real.sqrt t / 2) ^ 2 / 2) / y ≤ K) :
    ∫ y in Ioc (1 : ℝ) L, Phi y * (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2))
      ≤ Real.exp J * K / Real.sqrt (2 * π) * Real.exp ((n : ℝ) ^ 2 * t / 8) := by
  have hs0 : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hsq : (0 : ℝ) < Real.sqrt (2 * π) := Real.sqrt_pos.2 (by positivity)
  have hmono : ∫ y in Ioc (1 : ℝ) L, Phi y * (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2))
      ≤ ∫ y in Ioc (1 : ℝ) L, Real.exp J / Real.sqrt (2 * π)
          * Real.exp ((n : ℝ) ^ 2 * t / 8)
          * (Real.exp (-(y - (n : ℝ) * Real.sqrt t / 2) ^ 2 / 2) / y) := by
    refine setIntegral_mono_on hint1 hint2 measurableSet_Ioc (fun y hy => ?_)
    have hy0 : (0 : ℝ) < y := lt_trans zero_lt_one hy.1
    have hys : y * Real.sqrt t ≤ 1 / 2 := by
      refine le_trans ?_ hLs
      exact mul_le_mul_of_nonneg_right hy.2 hs0
    have h := integrand_le (n := n) ht hy0 hys (hJ y hy)
    refine le_trans h (le_of_eq ?_)
    field_simp
  refine le_trans hmono ?_
  rw [MeasureTheory.integral_const_mul]
  have hconst : (0 : ℝ) ≤ Real.exp J / Real.sqrt (2 * π) * Real.exp ((n : ℝ) ^ 2 * t / 8) := by
    positivity
  calc Real.exp J / Real.sqrt (2 * π) * Real.exp ((n : ℝ) ^ 2 * t / 8)
        * ∫ y in Ioc (1 : ℝ) L,
            Real.exp (-(y - (n : ℝ) * Real.sqrt t / 2) ^ 2 / 2) / y
      ≤ Real.exp J / Real.sqrt (2 * π) * Real.exp ((n : ℝ) ^ 2 * t / 8) * K :=
        mul_le_mul_of_nonneg_left hK hconst
    _ = Real.exp J * K / Real.sqrt (2 * π) * Real.exp ((n : ℝ) ^ 2 * t / 8) := by ring

/-- **The prefactor cancels.**  Eq. (56)'s prefactor is `n√t/2 = b`; the paper's Gaussian bound is
`K ≤ (2 + 2√(2π))/b`.  Their product is an absolute constant, with **no `n` and no `t` left**. -/
theorem prefactor_cancel {b K J : ℝ} (hb : 0 < b)
    (hK : K ≤ (2 + 2 * Real.sqrt (2 * π)) / b) :
    b * (Real.exp J * K / Real.sqrt (2 * π))
      ≤ Real.exp J * (2 / Real.sqrt (2 * π) + 2) := by
  have hsq : (0 : ℝ) < Real.sqrt (2 * π) := Real.sqrt_pos.2 (by positivity)
  have hbK : b * K ≤ 2 + 2 * Real.sqrt (2 * π) := by
    rw [← le_div_iff₀' hb]
    exact hK
  calc b * (Real.exp J * K / Real.sqrt (2 * π))
      = Real.exp J * (b * K) / Real.sqrt (2 * π) := by ring
    _ ≤ Real.exp J * (2 + 2 * Real.sqrt (2 * π)) / Real.sqrt (2 * π) := by
        gcongr
    _ = Real.exp J * (2 / Real.sqrt (2 * π) + 2) := by field_simp

end Submission.L10

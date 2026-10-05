/-
Gate L-10 (`klartag_packing`), brief 14.

**Lemma 4.3's `t`-integration**, the item report 10 §5 flagged as budgeted by nobody, plus the
remaining half of the domination profile.

Report 5 defines the contact weight as a `t`-integral,
`w y = ∫₀ᵀ Φ(t^{−1/2}(a₀ − 1/|αy|²))·1_{R_t}(αy) dt`, while reports 9 and 10 work at fixed `t`.
This module closes the gap.

**The arithmetic, exactly.**  At `T = 16·log n/n²` the exponent is `n²T/8 = 2·log n`, so
`e^{n²T/8} = n²` **on the nose**, and

  `∫₀ᵀ e^{n²t/8} dt = (8/n²)·(e^{n²T/8} − 1) = (8/n²)·(n² − 1) = 8 − 8/n² < 8`.

An absolute constant with no `n` in it.  That is Klartag's eq. (62) constant, and it is why the
first moment integrated over `(0,T]` stays `O(1)` — the fact report 2 §5.1 identified as the other
half of what pins `T`, alongside `n²T/4 = 4·log n`.  Every constant below is named; none is
asymptotic.
-/
import Submission.L10.Lemma43B

namespace Submission.L10

open MeasureTheory Set Real
open scoped ENNReal NNReal

/-! ## 1. The `t`-integral, exactly -/

/-- `∫₀^T e^{c·t} dt = (e^{c·T} − 1)/c`. -/
theorem integral_exp_mul_Ioc {c T : ℝ} (hc : c ≠ 0) (hT : 0 ≤ T) :
    ∫ t in Ioc (0 : ℝ) T, Real.exp (c * t) = (Real.exp (c * T) - 1) / c := by
  have hderiv : ∀ x ∈ uIcc (0 : ℝ) T, HasDerivAt (fun t : ℝ => Real.exp (c * t) / c)
      (Real.exp (c * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => c * t) c x := by
      simpa using (hasDerivAt_id x).const_mul c
    have h2 : HasDerivAt (fun t : ℝ => Real.exp (c * t)) (Real.exp (c * x) * c) x := h1.exp
    have h3 := h2.div_const c
    have heq : Real.exp (c * x) * c / c = Real.exp (c * x) := by field_simp
    rwa [heq] at h3
  have hint : IntervalIntegrable (fun t : ℝ => Real.exp (c * t)) volume 0 T :=
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [← intervalIntegral.integral_of_le hT, hFTC]
  simp
  field_simp

/-- With `T = 16·log n/n²`, the exponent is exactly `2·log n`, so `e^{n²T/8} = n²`. -/
theorem exp_n2T_eq {n : ℕ} (hn : 0 < n) {T : ℝ} (hT : T = 16 * Real.log n / (n : ℝ) ^ 2) :
    Real.exp ((n : ℝ) ^ 2 / 8 * T) = (n : ℝ) ^ 2 := by
  have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 hn
  have hexp : (n : ℝ) ^ 2 / 8 * T = 2 * Real.log n := by
    rw [hT]; field_simp; ring
  rw [hexp, two_mul, Real.exp_add, Real.exp_log hn0]
  ring

/-- **The `t`-integral of Lemma 4.3's bound, exactly.**  `∫₀ᵀ e^{n²t/8} dt = 8 − 8/n²`.

No asymptotics: this is an identity at `T = 16·log n/n²`.  Verified numerically against quadrature
to ten digits (`/private/tmp/claude-501/b-l10-2/t_integral.py`). -/
theorem integral_exp_n2_eq {n : ℕ} (hn : 0 < n) {T : ℝ}
    (hT : T = 16 * Real.log n / (n : ℝ) ^ 2) (hT0 : 0 ≤ T) :
    ∫ t in Ioc (0 : ℝ) T, Real.exp ((n : ℝ) ^ 2 / 8 * t) = 8 - 8 / (n : ℝ) ^ 2 := by
  have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 hn
  have hc : (n : ℝ) ^ 2 / 8 ≠ 0 := by positivity
  rw [integral_exp_mul_Ioc hc hT0, exp_n2T_eq hn hT]
  field_simp

/-- The bound actually used: the `t`-integral is below the absolute constant `8`. -/
theorem integral_exp_n2_le {n : ℕ} (hn : 0 < n) {T : ℝ}
    (hT : T = 16 * Real.log n / (n : ℝ) ^ 2) (hT0 : 0 ≤ T) :
    ∫ t in Ioc (0 : ℝ) T, Real.exp ((n : ℝ) ^ 2 / 8 * t) ≤ 8 := by
  rw [integral_exp_n2_eq hn hT hT0]
  have : (0 : ℝ) < (n : ℝ) ^ 2 := by
    have : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 hn
    positivity
  have h8 : (0 : ℝ) ≤ 8 / (n : ℝ) ^ 2 := by positivity
  linarith

/-- `T = 16·log n/n²` is non-negative for `n ≥ 1`. -/
theorem T_nonneg {n : ℕ} (hn : 1 ≤ n) : (0 : ℝ) ≤ 16 * Real.log n / (n : ℝ) ^ 2 := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog : (0 : ℝ) ≤ Real.log n := Real.log_nonneg hn1
  positivity

/-! ## 2. The domination profile's remaining half

`Lemma43B.dom_of_antitone` needs the profile antitone.  The `t`-integrated profile inherits that
from the fixed-`t` family, one `setIntegral_mono_on` away — this is the half report 10 §5 left. -/

section Antitone

/-- An integral of antitone functions is antitone. -/
theorem antitone_integral {T : ℝ} {g : ℝ → ℝ → ℝ}
    (hanti : ∀ t ∈ Ioc (0 : ℝ) T, Antitone (g t))
    (hint : ∀ r : ℝ, IntegrableOn (fun t : ℝ => g t r) (Ioc (0 : ℝ) T)) :
    Antitone (fun r : ℝ => ∫ t in Ioc (0 : ℝ) T, g t r) := by
  intro r₁ r₂ h
  exact setIntegral_mono_on (hint r₂) (hint r₁) measurableSet_Ioc (fun t ht => hanti t ht h)

/-- The `t`-integrated profile is non-negative. -/
theorem integral_nonneg_of_nonneg {T : ℝ} {g : ℝ → ℝ → ℝ} (hg0 : ∀ t r, 0 ≤ g t r) (r : ℝ) :
    0 ≤ ∫ t in Ioc (0 : ℝ) T, g t r :=
  setIntegral_nonneg measurableSet_Ioc (fun t _ => hg0 t r)

/-- **Domination for the `t`-integrated weight.**  Combining `antitone_integral` with
`Lemma43B.dom_of_antitone`: the widened, `t`-integrated profile dominates at every point of every
cube, not just at the centre. -/
theorem dom_of_antitone_integral {n : ℕ} (hn : 0 < n) {T : ℝ} {g : ℝ → ℝ → ℝ}
    (hanti : ∀ t ∈ Ioc (0 : ℝ) T, Antitone (g t))
    (hint : ∀ r : ℝ, IntegrableOn (fun t : ℝ => g t r) (Ioc (0 : ℝ) T))
    (B : Finset (Fin n → ℤ)) :
    ∀ y ∈ B, ∀ x ∈ Tiling.cube (Tiling.toE n y),
      ENNReal.ofReal (∫ t in Ioc (0 : ℝ) T, g t ‖Tiling.toE n y‖)
        ≤ ENNReal.ofReal (∫ t in Ioc (0 : ℝ) T, g t (‖x‖ - Real.sqrt n / 2)) :=
  dom_of_antitone hn (antitone_integral hanti hint) B

end Antitone

/-! ## 3. Tonelli, and the `t`-integrated radial bound

Everything in reports 9 and 10 is at fixed `t`.  Swapping the `y`- and `t`-integrals in `ℝ≥0∞`
costs only joint `AEMeasurable` — no integrability — which is why the swap is done here and the
Bochner statement is recovered afterwards. -/

section Tonelli

/-- **Tonelli for the radial/`t` pair.**  The `ℝ≥0∞` swap; only measurability is needed. -/
theorem lintegral_radial_t_swap {T : ℝ} (G : ℝ → ℝ → ℝ≥0∞)
    (hG : AEMeasurable (Function.uncurry G)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioc (0 : ℝ) T)))) :
    ∫⁻ y in Ioi (0 : ℝ), ∫⁻ t in Ioc (0 : ℝ) T, G y t
      = ∫⁻ t in Ioc (0 : ℝ) T, ∫⁻ y in Ioi (0 : ℝ), G y t :=
  lintegral_lintegral_swap hG

/-- **The `t`-integrated radial bound in `ℝ≥0∞`.**  Feed the fixed-`t` Lemma 4.3 bound
`∫ y ≤ C₁·e^{n²t/8}` and get `∫ y ∫ t ≤ C₁·(8 − 8/n²)` — the exact constant of §1. -/
theorem lintegral_radial_t_le {n : ℕ} (hn : 0 < n) {T C₁ : ℝ}
    (hT : T = 16 * Real.log n / (n : ℝ) ^ 2) (hT0 : 0 ≤ T) (hC₁ : 0 ≤ C₁)
    (G : ℝ → ℝ → ℝ≥0∞)
    (hG : AEMeasurable (Function.uncurry G)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioc (0 : ℝ) T))))
    (hbound : ∀ t ∈ Ioc (0 : ℝ) T, ∫⁻ y in Ioi (0 : ℝ), G y t
      ≤ ENNReal.ofReal (C₁ * Real.exp ((n : ℝ) ^ 2 / 8 * t))) :
    ∫⁻ y in Ioi (0 : ℝ), ∫⁻ t in Ioc (0 : ℝ) T, G y t
      ≤ ENNReal.ofReal (C₁ * (8 - 8 / (n : ℝ) ^ 2)) := by
  have hcont : Continuous (fun t : ℝ => C₁ * Real.exp ((n : ℝ) ^ 2 / 8 * t)) := by fun_prop
  have hintOn : IntegrableOn (fun t : ℝ => C₁ * Real.exp ((n : ℝ) ^ 2 / 8 * t))
      (Ioc (0 : ℝ) T) := hcont.integrableOn_Ioc
  have hnn : ∀ t : ℝ, 0 ≤ C₁ * Real.exp ((n : ℝ) ^ 2 / 8 * t) := by
    intro t; positivity
  have hval : ∫ t in Ioc (0 : ℝ) T, C₁ * Real.exp ((n : ℝ) ^ 2 / 8 * t)
      = C₁ * (8 - 8 / (n : ℝ) ^ 2) := by
    rw [MeasureTheory.integral_const_mul, integral_exp_n2_eq hn hT hT0]
  calc ∫⁻ y in Ioi (0 : ℝ), ∫⁻ t in Ioc (0 : ℝ) T, G y t
      = ∫⁻ t in Ioc (0 : ℝ) T, ∫⁻ y in Ioi (0 : ℝ), G y t := lintegral_radial_t_swap G hG
    _ ≤ ∫⁻ t in Ioc (0 : ℝ) T,
          ENNReal.ofReal (C₁ * Real.exp ((n : ℝ) ^ 2 / 8 * t)) := by
        refine setLIntegral_mono (hcont.measurable.ennreal_ofReal) (fun t ht => hbound t ht)
    _ = ENNReal.ofReal (∫ t in Ioc (0 : ℝ) T, C₁ * Real.exp ((n : ℝ) ^ 2 / 8 * t)) :=
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hintOn
          (Filter.Eventually.of_forall (fun t => hnn t))).symm
    _ = ENNReal.ofReal (C₁ * (8 - 8 / (n : ℝ) ^ 2)) := by rw [hval]

/-- **From an `ℝ≥0∞` bound to `RadialWeightData.radial_bound`.**  The Bochner statement the
structure wants, recovered from the `ℝ≥0∞` one under integrability. -/
theorem radial_bound_of_lintegral {n : ℕ} {f : ℝ → ℝ} {C : ℝ}
    (hf0 : ∀ r : ℝ, 0 ≤ f r) (hC0 : 0 ≤ C)
    (hint : IntegrableOn (fun y : ℝ => y ^ (n - 1) * f y) (Ioi (0 : ℝ)))
    (hlint : ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (y ^ (n - 1) * f y) ≤ ENNReal.ofReal C) :
    ∫ y in Ioi (0 : ℝ), y ^ (n - 1) * f y ≤ C := by
  have hbridge := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
    (by filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with y hy
        exact mul_nonneg (pow_nonneg (le_of_lt hy) _) (hf0 y))
  rw [← hbridge] at hlint
  exact (ENNReal.ofReal_le_ofReal_iff hC0).1 hlint

end Tonelli

/-! ## 4. `RadialWeightData` from the chain's parameters

The structure brief 13's `chainData_of_params` consumes.  Every hypothesis is named; nothing is
asymptotic, and the only size condition is `n ≥ 1`. -/

section Assembly

open Submission.L10.Section5 Submission.L10.Tiling

/-- Pulling `y^{n−1}` and the `t`-integral through `ENNReal.ofReal`. -/
theorem lintegral_t_ofReal {n : ℕ} {T y : ℝ} (hy : 0 ≤ y) {g : ℝ → ℝ → ℝ}
    (hg0 : ∀ t r : ℝ, 0 ≤ g t r)
    (hint : IntegrableOn (fun t : ℝ => g t y) (Ioc (0 : ℝ) T)) :
    ∫⁻ t in Ioc (0 : ℝ) T, ENNReal.ofReal (y ^ (n - 1) * g t y)
      = ENNReal.ofReal (y ^ (n - 1) * ∫ t in Ioc (0 : ℝ) T, g t y) := by
  have hc : (0 : ℝ) ≤ y ^ (n - 1) := pow_nonneg hy _
  have hfun : (fun t : ℝ => ENNReal.ofReal (y ^ (n - 1) * g t y))
      = fun t : ℝ => ENNReal.ofReal (y ^ (n - 1)) * ENNReal.ofReal (g t y) := by
    funext t
    rw [ENNReal.ofReal_mul hc]
  rw [hfun, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall (fun t => hg0 t y)),
    ← ENNReal.ofReal_mul hc]

/-- `8 − 8/n² ≥ 0` for `n ≥ 1`. -/
theorem eight_sub_nonneg {n : ℕ} (hn : 0 < n) : (0 : ℝ) ≤ 8 - 8 / (n : ℝ) ^ 2 := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have : 8 / (n : ℝ) ^ 2 ≤ 8 := by
    rw [div_le_iff₀ (by nlinarith)]
    nlinarith
  linarith

/-- **`RadialWeightData` from the chain's parameters.**

Inputs, in order: the dimension `n ≥ 1`; the horizon `T = 16·log n/n²` and Lemma 4.3's constant
`C₁`; the fixed-`t` widened radial profile family `g`, with its non-negativity, its `t`-integrability
at each radius, joint measurability for Tonelli, and the **fixed-`t` Lemma 4.3 bound**
`∫ y^{n−1}·g t y dy ≤ C₁·e^{n²t/8}`; the contact weight `w` on its support with worst-point
domination; two integrability certificates; and Markov's threshold.

The `C` it produces is `C₁·(8 − 8/n²)` — the exact `t`-integral of §1, an absolute constant. -/
noncomputable def radialWeightData_of_chain {p n : ℕ} (hn : 0 < n) {T C₁ : ℝ}
    (hT : T = 16 * Real.log n / (n : ℝ) ^ 2) (hC₁ : 0 ≤ C₁)
    {g : ℝ → ℝ → ℝ} (hg0 : ∀ t r : ℝ, 0 ≤ g t r)
    (hgt : ∀ r : ℝ, IntegrableOn (fun t : ℝ => g t r) (Ioc (0 : ℝ) T))
    (hgmeas : AEMeasurable
      (Function.uncurry (fun y t : ℝ => ENNReal.ofReal (y ^ (n - 1) * g t y)))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioc (0 : ℝ) T))))
    (hgbound : ∀ t ∈ Ioc (0 : ℝ) T,
      ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (y ^ (n - 1) * g t y)
        ≤ ENNReal.ofReal (C₁ * Real.exp ((n : ℝ) ^ 2 / 8 * t)))
    (w : (Fin n → ℤ) → ℝ≥0∞) (supp : Finset (Fin n → ℤ))
    (hdom : ∀ y ∈ supp, ∀ x ∈ cube (toE n y),
      w y ≤ ENNReal.ofReal (∫ t in Ioc (0 : ℝ) T, g t ‖x‖))
    (hxint : Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      ∫ t in Ioc (0 : ℝ) T, g t ‖x‖))
    (hyint : IntegrableOn
      (fun y : ℝ => y ^ (n - 1) * ∫ t in Ioc (0 : ℝ) T, g t y) (Ioi (0 : ℝ)))
    (theta : ℝ≥0∞)
    (hmarkov : 2 * (((p - 1 : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal ((n : ℝ) * kappa n * (C₁ * (8 - 8 / (n : ℝ) ^ 2))))
      < theta * ((p ^ n - 1 : ℕ) : ℝ≥0∞)) :
    RadialWeightData p n where
  f := fun r => ∫ t in Ioc (0 : ℝ) T, g t r
  f_nonneg := fun r => integral_nonneg_of_nonneg hg0 r
  w := w
  supp := supp
  dom := hdom
  integrable := hxint
  C := C₁ * (8 - 8 / (n : ℝ) ^ 2)
  radial_bound := by
    refine radial_bound_of_lintegral (fun r => integral_nonneg_of_nonneg hg0 r)
      (mul_nonneg hC₁ (eight_sub_nonneg hn)) hyint ?_
    have hcongr : ∫⁻ y in Ioi (0 : ℝ),
          ENNReal.ofReal (y ^ (n - 1) * ∫ t in Ioc (0 : ℝ) T, g t y)
        = ∫⁻ y in Ioi (0 : ℝ), ∫⁻ t in Ioc (0 : ℝ) T,
            ENNReal.ofReal (y ^ (n - 1) * g t y) := by
      refine (setLIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_))
      exact (lintegral_t_ofReal (n := n) (le_of_lt hy) hg0 (hgt y)).symm
    rw [hcongr]
    exact lintegral_radial_t_le hn hT (hT ▸ T_nonneg hn) hC₁ _ hgmeas hgbound
  theta := theta
  markov := hmarkov

/-- **The hand-off: `ChainData.weight_bound` from the chain's parameters.**

Composing `radialWeightData_of_chain` with `Lemma43B.weight_bound_of_params`.  This is the
statement brief 13's `chainData_of_params` needs; every input is a named hypothesis of the chain's
own data, and the constant is `C₁·(8 − 8/n²)`. -/
theorem weight_bound_of_chain {p n : ℕ} [Fact (Nat.Prime p)] (hn : 0 < n) {T C₁ : ℝ}
    (hT : T = 16 * Real.log n / (n : ℝ) ^ 2) (hC₁ : 0 ≤ C₁)
    {g : ℝ → ℝ → ℝ} (hg0 : ∀ t r : ℝ, 0 ≤ g t r)
    (hgt : ∀ r : ℝ, IntegrableOn (fun t : ℝ => g t r) (Ioc (0 : ℝ) T))
    (hgmeas : AEMeasurable
      (Function.uncurry (fun y t : ℝ => ENNReal.ofReal (y ^ (n - 1) * g t y)))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioc (0 : ℝ) T))))
    (hgbound : ∀ t ∈ Ioc (0 : ℝ) T,
      ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (y ^ (n - 1) * g t y)
        ≤ ENNReal.ofReal (C₁ * Real.exp ((n : ℝ) ^ 2 / 8 * t)))
    (w : (Fin n → ℤ) → ℝ≥0∞) (supp : Finset (Fin n → ℤ))
    (hdom : ∀ y ∈ supp, ∀ x ∈ cube (toE n y),
      w y ≤ ENNReal.ofReal (∫ t in Ioc (0 : ℝ) T, g t ‖x‖))
    (hxint : Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      ∫ t in Ioc (0 : ℝ) T, g t ‖x‖))
    (hyint : IntegrableOn
      (fun y : ℝ => y ^ (n - 1) * ∫ t in Ioc (0 : ℝ) T, g t y) (Ioi (0 : ℝ)))
    (theta : ℝ≥0∞)
    (hmarkov : 2 * (((p - 1 : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal ((n : ℝ) * kappa n * (C₁ * (8 - 8 / (n : ℝ) ^ 2))))
      < theta * ((p ^ n - 1 : ℕ) : ℝ≥0∞)) :
    2 * (((p - 1 : ℕ) : ℝ≥0∞) * ∑ y ∈ supp, w y) < theta * ((p ^ n - 1 : ℕ) : ℝ≥0∞) :=
  weight_bound_of_params hn
    (radialWeightData_of_chain hn hT hC₁ hg0 hgt hgmeas hgbound w supp hdom hxint hyint
      theta hmarkov)

end Assembly

/-! ## 5. The two fields brief 13 needs, and the `supp_indivisible` discharge

Report 13 §5.3 observed that `Lemma43B.RadialWeightData` is field-for-field its `Params`'
Lemma 4.3 block **except** for `supp_ne_zero` and `supp_radius`, which §5 needs in order to
discharge `ChainData.supp_indivisible` through `Section5.redMod_ne_zero_of_norm_lt` — and that
there is no other route, because a `p`-divisible point in the support breaks the first-moment
lemma's hypothesis.

`Lemma43B.lean` is reported and therefore frozen (rule 5), so the fields are added here in a
successor structure. **Field names match `ChainDataInst.Params` exactly**
(`windowRadius`, `window_lt_p`, `supp_ne_zero`, `supp_radius`, `theta_ne_zero`, `theta_ne_top`), so
`chainData_of_params` maps across with no renegotiation.  `theta_ne_zero` and `theta_ne_top` are
included for the same reason: `Params` has them, `RadialWeightData` does not, and `ChainData`
needs them. -/

section Successor

open Submission.L10.Section5 Submission.L10.Tiling Submission.L10.ConstructionA

/-- `RadialWeightData` plus the six fields `ChainDataInst.Params` carries and it does not. -/
structure RadialWeightData' (p n : ℕ) extends RadialWeightData p n where
  /-- The window radius; `supp` lies inside it and it is below `p`. -/
  windowRadius : ℝ
  window_lt_p : windowRadius < (p : ℝ)
  supp_ne_zero : ∀ y ∈ supp, y ≠ 0
  supp_radius : ∀ y ∈ supp, ‖toE n y‖ ≤ windowRadius
  theta_ne_zero : theta ≠ 0
  theta_ne_top : theta ≠ ⊤

/-- **`ChainData.supp_indivisible`, discharged.**  This is the seam report 13 §5.3 named: from
`supp_ne_zero` and `supp_radius` below a window strictly inside `p`, no support point is
`p`-divisible. -/
theorem supp_indivisible_of_data {p n : ℕ} [NeZero p] (d : RadialWeightData' p n) :
    ∀ y ∈ d.supp, redMod p y ≠ 0 := by
  intro y hy
  refine redMod_ne_zero_of_norm_lt (d.supp_ne_zero y hy) ?_
  exact lt_of_le_of_lt (d.supp_radius y hy) d.window_lt_p

/-- `weight_bound` from the successor structure — `Lemma43B.weight_bound_of_params` on the
inherited part. -/
theorem weight_bound_of_params' {p n : ℕ} [Fact (Nat.Prime p)] (hn : 0 < n)
    (d : RadialWeightData' p n) :
    2 * (((p - 1 : ℕ) : ℝ≥0∞) * ∑ y ∈ d.supp, d.w y) < d.theta * ((p ^ n - 1 : ℕ) : ℝ≥0∞) :=
  weight_bound_of_params hn d.toRadialWeightData

/-- **`RadialWeightData'` from the chain's parameters.**  `radialWeightData_of_chain` plus the six
fields; the extra hypotheses are exactly `ChainDataInst.Params`' own. -/
noncomputable def radialWeightData'_of_chain {p n : ℕ} (hn : 0 < n) {T C₁ : ℝ}
    (hT : T = 16 * Real.log n / (n : ℝ) ^ 2) (hC₁ : 0 ≤ C₁)
    {g : ℝ → ℝ → ℝ} (hg0 : ∀ t r : ℝ, 0 ≤ g t r)
    (hgt : ∀ r : ℝ, IntegrableOn (fun t : ℝ => g t r) (Ioc (0 : ℝ) T))
    (hgmeas : AEMeasurable
      (Function.uncurry (fun y t : ℝ => ENNReal.ofReal (y ^ (n - 1) * g t y)))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioc (0 : ℝ) T))))
    (hgbound : ∀ t ∈ Ioc (0 : ℝ) T,
      ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (y ^ (n - 1) * g t y)
        ≤ ENNReal.ofReal (C₁ * Real.exp ((n : ℝ) ^ 2 / 8 * t)))
    (w : (Fin n → ℤ) → ℝ≥0∞) (supp : Finset (Fin n → ℤ))
    (hdom : ∀ y ∈ supp, ∀ x ∈ cube (toE n y),
      w y ≤ ENNReal.ofReal (∫ t in Ioc (0 : ℝ) T, g t ‖x‖))
    (hxint : Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      ∫ t in Ioc (0 : ℝ) T, g t ‖x‖))
    (hyint : IntegrableOn
      (fun y : ℝ => y ^ (n - 1) * ∫ t in Ioc (0 : ℝ) T, g t y) (Ioi (0 : ℝ)))
    (theta : ℝ≥0∞)
    (hmarkov : 2 * (((p - 1 : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal ((n : ℝ) * kappa n * (C₁ * (8 - 8 / (n : ℝ) ^ 2))))
      < theta * ((p ^ n - 1 : ℕ) : ℝ≥0∞))
    (windowRadius : ℝ) (hwp : windowRadius < (p : ℝ))
    (hsupp0 : ∀ y ∈ supp, y ≠ 0)
    (hsuppR : ∀ y ∈ supp, ‖toE n y‖ ≤ windowRadius)
    (hθ0 : theta ≠ 0) (hθtop : theta ≠ ⊤) :
    RadialWeightData' p n where
  toRadialWeightData := radialWeightData_of_chain hn hT hC₁ hg0 hgt hgmeas hgbound w supp
    hdom hxint hyint theta hmarkov
  windowRadius := windowRadius
  window_lt_p := hwp
  supp_ne_zero := hsupp0
  supp_radius := hsuppR
  theta_ne_zero := hθ0
  theta_ne_top := hθtop

end Successor

/-! ## 6. H9's per-point input: the tail plus the excursion term

`ChainDataInst.expected_card_le` wants `htail : μ.real {ω | i ∈ C ω} ≤ 2·weight i + err i`.
Report 13 §5.2 leaves both inputs here.  The per-point tail is `Padding.padded_tail_of_increments`
(brief 8), whose constant is `4 = 2·2`, i.e. `weight i = 2·Φ(…)`.  That bound holds on the good
event; off it the chain may have left the shell, and the paper's `Ce^{−cn}` (Prop 4.2, eq. 53) is
the price.  `GoodEvent.measureReal_compl_goodEvent_chainScale` (report 12) supplies that number.

The lemma below is the composition, and it is all that stands between the two inputs and `htail`. -/

section Excursion

/-- **Tail plus excursion.**  A per-point bound valid on a good event, plus the measure of the bad
event, gives exactly `expected_card_le`'s `2·weight + err` shape. -/
theorem tail_add_excursion {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {A Gd : Set Ω}
    {wgt err : ℝ} (hgood : P.real (A ∩ Gd) ≤ 2 * wgt) (hexc : P.real Gdᶜ ≤ err) :
    P.real A ≤ 2 * wgt + err := by
  have hsub : A ⊆ (A ∩ Gd) ∪ Gdᶜ := by
    intro ω hω
    by_cases hg : ω ∈ Gd
    · exact Or.inl ⟨hω, hg⟩
    · exact Or.inr hg
  calc P.real A ≤ P.real ((A ∩ Gd) ∪ Gdᶜ) :=
        measureReal_mono hsub (by finiteness)
    _ ≤ P.real (A ∩ Gd) + P.real Gdᶜ := measureReal_union_le _ _
    _ ≤ 2 * wgt + err := by linarith

end Excursion

end Submission.L10

/-
Gate L-10 (`klartag_packing`), brief 10.

**Finishing Lemma 4.3**: the Gaussian integral left open by report 9 §6, the polar change of
variables, and the domination profile widened to the cube's worst point.

Report 9 proved the load-bearing half — the `1/8` — and reduced Klartag's `I₂` (p. 20-21, eq. 59) to
a single Gaussian integral carrying no `n`.  This module closes that integral and carries the result
to a statement the chain can instantiate from its own parameters.
-/
import Submission.L10.Lemma43
import Submission.L10.Section5

namespace Submission.L10

open MeasureTheory Set Real
open scoped ENNReal NNReal

/-! ## 1. Two elementary bounds -/

/-- `s·e^{-s} ≤ e⁻¹` for every real `s`.  One application of `1 + x ≤ e^x` at `x = s - 1`. -/
theorem mul_exp_neg_le (s : ℝ) : s * Real.exp (-s) ≤ Real.exp (-1) := by
  have hkey : s ≤ Real.exp (s - 1) := by
    have := Real.add_one_le_exp (s - 1)
    linarith
  calc s * Real.exp (-s) ≤ Real.exp (s - 1) * Real.exp (-s) :=
        mul_le_mul_of_nonneg_right hkey (Real.exp_pos _).le
    _ = Real.exp (-1) := by rw [← Real.exp_add]; ring_nf

/-- `b²·e^{-b²/8} ≤ 4`.  This is what makes the near piece of the split integrate to `≤ 2/b`. -/
theorem sq_mul_exp_le_four (b : ℝ) : b ^ 2 * Real.exp (-b ^ 2 / 8) ≤ 4 := by
  have h := mul_exp_neg_le (b ^ 2 / 8)
  have h1 : (2 : ℝ) < Real.exp 1 := by
    have hhalf : (3 : ℝ) / 2 ≤ Real.exp (1 / 2) := by
      have := Real.add_one_le_exp (1 / 2 : ℝ); linarith
    have hsq : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [hhalf, hsq]
  have he : Real.exp (-1) ≤ 1 / 2 := by
    have hprod : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (-1), h1, hprod]
  have hneg : -(b ^ 2 / 8) = -b ^ 2 / 8 := by ring
  rw [hneg] at h
  nlinarith [h, he, Real.exp_pos (-b ^ 2 / 8)]

/-! ## 2. The Gaussian integral

`∫₁^L e^{-(y-b)²/2}/y dy ≤ (2 + 2√(2π))/b`, split at `b/2`:
* on `(1, b/2]`, `1/y ≤ 1` and `(y-b)² ≥ b²/4`, so the integrand is `≤ e^{-b²/8}` and the piece is
  at most `(b/2)·e^{-b²/8} ≤ 2/b` by `sq_mul_exp_le_four`;
* on `(b/2, L]`, `1/y ≤ 2/b` and the Gaussian has total mass `√(2π)`.
-/

/-- The total mass of the shifted Gaussian. -/
theorem integral_shifted_gaussian (b : ℝ) :
    ∫ y : ℝ, Real.exp (-(y - b) ^ 2 / 2) = Real.sqrt (2 * π) := by
  have hfun : (fun y : ℝ => Real.exp (-(y - b) ^ 2 / 2))
      = fun y : ℝ => (fun u : ℝ => Real.exp (-(1 / 2) * u ^ 2)) (y - b) := by
    funext y; congr 1; ring
  rw [hfun, MeasureTheory.integral_sub_right_eq_self
    (fun u : ℝ => Real.exp (-(1 / 2) * u ^ 2)) b, integral_gaussian]
  rw [show π / (1 / 2) = 2 * π by ring]

theorem integrable_shifted_gaussian (b : ℝ) :
    Integrable (fun y : ℝ => Real.exp (-(y - b) ^ 2 / 2)) := by
  have h := integrable_exp_neg_mul_sq (b := 1 / 2) (by norm_num)
  have h2 := h.comp_sub_right b
  have hfun : (fun y : ℝ => Real.exp (-(1 / 2) * (y - b) ^ 2))
      = fun y : ℝ => Real.exp (-(y - b) ^ 2 / 2) := by
    funext y; congr 1; ring
  rwa [hfun] at h2

theorem continuousOn_gaussian_div {b : ℝ} {L : ℝ} :
    ContinuousOn (fun y : ℝ => Real.exp (-(y - b) ^ 2 / 2) / y) (Icc 1 L) := by
  refine ContinuousOn.div (by fun_prop) continuousOn_id (fun y hy => ?_)
  have : (1 : ℝ) ≤ y := hy.1
  linarith

theorem integrableOn_gaussian_div {b L : ℝ} {s : Set ℝ} (hs : s ⊆ Icc 1 L) :
    IntegrableOn (fun y : ℝ => Real.exp (-(y - b) ^ 2 / 2) / y) s := by
  have hIcc : IntegrableOn (fun y : ℝ => Real.exp (-(y - b) ^ 2 / 2) / y) (Icc 1 L) :=
    (continuousOn_gaussian_div (b := b) (L := L)).integrableOn_compact isCompact_Icc
  exact hIcc.mono_set hs

/-- **The Gaussian integral.**  This is the one fact report 9 §6 left open. -/
theorem gaussian_over_y_le {b L : ℝ} (hb : 2 ≤ b) (hL : b / 2 ≤ L) :
    ∫ y in Ioc (1 : ℝ) L, Real.exp (-(y - b) ^ 2 / 2) / y
      ≤ (2 + 2 * Real.sqrt (2 * π)) / b := by
  have hb0 : (0 : ℝ) < b := by linarith
  have h1b : (1 : ℝ) ≤ b / 2 := by linarith
  have hsplit : Ioc (1 : ℝ) L = Ioc (1 : ℝ) (b / 2) ∪ Ioc (b / 2) L :=
    (Ioc_union_Ioc_eq_Ioc h1b hL).symm
  have hsub1 : Ioc (1 : ℝ) (b / 2) ⊆ Icc 1 L := by
    intro y hy; exact ⟨hy.1.le, le_trans hy.2 hL⟩
  have hsub2 : Ioc (b / 2) L ⊆ Icc 1 L := by
    intro y hy; exact ⟨le_trans h1b hy.1.le, hy.2⟩
  have hi1 := integrableOn_gaussian_div (b := b) (L := L) hsub1
  have hi2 := integrableOn_gaussian_div (b := b) (L := L) hsub2
  have hdisj : Disjoint (Ioc (1 : ℝ) (b / 2)) (Ioc (b / 2) L) :=
    Set.disjoint_left.2 (fun y hy1 hy2 => absurd hy2.1 (not_lt.2 hy1.2))
  rw [hsplit, setIntegral_union hdisj measurableSet_Ioc hi1 hi2]
  -- near piece
  have hnear : ∫ y in Ioc (1 : ℝ) (b / 2), Real.exp (-(y - b) ^ 2 / 2) / y ≤ 2 / b := by
    have hbound : ∫ y in Ioc (1 : ℝ) (b / 2), Real.exp (-(y - b) ^ 2 / 2) / y
        ≤ ∫ _y in Ioc (1 : ℝ) (b / 2), Real.exp (-b ^ 2 / 8) := by
      refine setIntegral_mono_on hi1 (continuous_const.integrableOn_Ioc)
        measurableSet_Ioc (fun y hy => ?_)
      have hy1 : (1 : ℝ) ≤ y := hy.1.le
      have hy0 : (0 : ℝ) < y := by linarith
      have hgap : b ^ 2 / 4 ≤ (y - b) ^ 2 := by nlinarith [hy.2, hb0]
      calc Real.exp (-(y - b) ^ 2 / 2) / y ≤ Real.exp (-(y - b) ^ 2 / 2) / 1 := by
            gcongr
        _ = Real.exp (-(y - b) ^ 2 / 2) := by ring
        _ ≤ Real.exp (-b ^ 2 / 8) := Real.exp_le_exp.2 (by linarith)
    refine le_trans hbound ?_
    have hvol : (volume.real (Ioc (1 : ℝ) (b / 2))) = b / 2 - 1 := by
      rw [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
    rw [setIntegral_const, hvol, smul_eq_mul, le_div_iff₀ hb0]
    have hkey := sq_mul_exp_le_four b
    nlinarith [Real.exp_pos (-b ^ 2 / 8), hkey, hb0]
  -- far piece
  have hfar : ∫ y in Ioc (b / 2) L, Real.exp (-(y - b) ^ 2 / 2) / y
      ≤ 2 * Real.sqrt (2 * π) / b := by
    have hbound : ∫ y in Ioc (b / 2) L, Real.exp (-(y - b) ^ 2 / 2) / y
        ≤ ∫ y in Ioc (b / 2) L, 2 / b * Real.exp (-(y - b) ^ 2 / 2) := by
      refine setIntegral_mono_on hi2 (((integrable_shifted_gaussian b).const_mul _).integrableOn)
        measurableSet_Ioc (fun y hy => ?_)
      have hy0 : (0 : ℝ) < y := by linarith [hy.1]
      have hinv : 1 / y ≤ 2 / b := by
        rw [div_le_iff₀ hy0, ← sub_nonneg]
        have hfe : 2 / b * y - 1 = (2 * y - b) / b := by field_simp
        rw [hfe]
        exact div_nonneg (by linarith [hy.1]) hb0.le
      calc Real.exp (-(y - b) ^ 2 / 2) / y = Real.exp (-(y - b) ^ 2 / 2) * (1 / y) := by ring
        _ ≤ Real.exp (-(y - b) ^ 2 / 2) * (2 / b) := by
            exact mul_le_mul_of_nonneg_left hinv (Real.exp_pos _).le
        _ = 2 / b * Real.exp (-(y - b) ^ 2 / 2) := by ring
    refine le_trans hbound ?_
    rw [MeasureTheory.integral_const_mul]
    have hmass : ∫ y in Ioc (b / 2) L, Real.exp (-(y - b) ^ 2 / 2) ≤ Real.sqrt (2 * π) := by
      rw [← integral_shifted_gaussian b]
      exact setIntegral_le_integral (integrable_shifted_gaussian b)
        (Filter.Eventually.of_forall (fun y => (Real.exp_pos _).le))
    calc 2 / b * ∫ y in Ioc (b / 2) L, Real.exp (-(y - b) ^ 2 / 2)
        ≤ 2 / b * Real.sqrt (2 * π) := by
          refine mul_le_mul_of_nonneg_left hmass (by positivity)
      _ = 2 * Real.sqrt (2 * π) / b := by ring
  have : (2 : ℝ) / b + 2 * Real.sqrt (2 * π) / b = (2 + 2 * Real.sqrt (2 * π)) / b := by ring
  linarith [hnear, hfar, this.ge, this.le]

/-! ## 3. Domination at the cube's worst point

Report 9 §5 flagged the trap: for a **radial** `ψ`, `Section5.weight_bound_of_lintegral`'s `hdom`
must hold at the cube's *worst* point, not its centre, and `Φ(y(r))` is antitone only for
`r ≥ 1/√a₀`.  The constructive fix is here, and it is generic: take any antitone `g` and shift its
argument inward by the cube radius `√n/2`.  Then `f r := g (r − √n/2)` dominates `g ‖toE n y‖` on
the entire cube at `y`, because every `x` in that cube has `‖x‖ < ‖toE n y‖ + √n/2`.

Antitonicity of the *truncated* profile — capped at `Φ(0) = 1/2` below the inner radius — is what
the chain must supply; `capped_antitone` below is the shape, and the cap is what removes the
`Φ 0 = 0` artifact (`Real`'s `1/0 = 0` makes the uncapped `Phi` discontinuous at `0`). -/

section Domination

open Submission.L10.Tiling

variable {n : ℕ}

/-- Every point of the unit cube at `y` has norm within `√n/2` of `‖y‖`. -/
theorem norm_le_of_mem_cube (hn : 0 < n) (y : Fin n → ℤ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ cube (toE n y)) :
    ‖x‖ ≤ ‖toE n y‖ + Real.sqrt n / 2 := by
  have h := norm_sub_lt_of_mem_cube hn (toE n y) hx
  have := norm_sub_norm_le x (toE n y)
  linarith

/-- **Worst-point domination from antitonicity.**  With `f r = g (r − √n/2)` for an antitone `g`,
the weight `g ‖toE n y‖` is dominated by `f ‖x‖` at *every* `x` in the cube at `y`. -/
theorem dom_of_antitone (hn : 0 < n) {g : ℝ → ℝ} (hg : Antitone g)
    (B : Finset (Fin n → ℤ)) :
    ∀ y ∈ B, ∀ x ∈ cube (toE n y),
      ENNReal.ofReal (g ‖toE n y‖) ≤ ENNReal.ofReal (g (‖x‖ - Real.sqrt n / 2)) := by
  intro y _ x hx
  refine ENNReal.ofReal_le_ofReal (hg ?_)
  have := norm_le_of_mem_cube hn y hx
  linarith

/-- The capped profile `r ↦ min c (g r)` is antitone whenever `g` is, and never exceeds `c`.
This is how `Φ`'s value at the shell's inner radius is handled: cap at `Φ(0) = 1/2` rather than
evaluate `Phi 0`, which is `0` in Lean because `1/0 = 0`. -/
theorem capped_antitone {g : ℝ → ℝ} (hg : Antitone g) (c : ℝ) :
    Antitone (fun r => min c (g r)) := fun _ _ h => min_le_min le_rfl (hg h)

end Domination

/-! ## 4. The parameter interface

Everything Lemma 4.3 must hand §5, as one structure.  `weight_bound_of_params` turns it into
`Section5.ChainData.weight_bound` verbatim, so brief 7's chain can populate `ChainData` without
renegotiating the boundary. -/

section Params

open Submission.L10.Section5 Submission.L10.Tiling

/-- **What the chain owes Lemma 4.3's consumer.**  Eight fields, and nothing else. -/
structure RadialWeightData (p n : ℕ) where
  /-- The radial profile, already widened to the cube's worst point (`§3`). -/
  f : ℝ → ℝ
  f_nonneg : ∀ r : ℝ, 0 ≤ f r
  /-- Eq. (65)'s contact weight and its finite support. -/
  w : (Fin n → ℤ) → ℝ≥0∞
  supp : Finset (Fin n → ℤ)
  /-- Domination **at every point of the cube**, not just its centre — see `dom_of_antitone`. -/
  dom : ∀ y ∈ supp, ∀ x ∈ cube (toE n y), w y ≤ ENNReal.ofReal (f ‖x‖)
  /-- Integrability, needed because `integral_fun_norm_addHaar` is a Bochner integral. -/
  integrable : Integrable (fun x : EuclideanSpace ℝ (Fin n) => f ‖x‖)
  /-- Lemma 4.3's number: `C = C₁·e^{n²T/8}/n` in the paper's notation. -/
  C : ℝ
  radial_bound : ∫ y in Ioi (0 : ℝ), y ^ (n - 1) * f y ≤ C
  /-- Markov's threshold. -/
  theta : ℝ≥0∞
  markov : 2 * (((p - 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal ((n : ℝ) * kappa n * C))
      < theta * ((p ^ n - 1 : ℕ) : ℝ≥0∞)

/-- **`ChainData.weight_bound` from the parameters.**  This is the hand-off: given
`RadialWeightData`, the Markov-threshold field of `Section5.ChainData` is discharged. -/
theorem weight_bound_of_params {p n : ℕ} [Fact (Nat.Prime p)] (hn : 0 < n)
    (d : RadialWeightData p n) :
    2 * (((p - 1 : ℕ) : ℝ≥0∞) * ∑ y ∈ d.supp, d.w y) < d.theta * ((p ^ n - 1 : ℕ) : ℝ≥0∞) :=
  weight_bound_of_radial hn d.supp d.w d.f d.f_nonneg d.dom d.integrable d.radial_bound
    d.theta d.markov

end Params

/-! ## 5. The polar change of variables

Klartag substitutes `y = t^{−1/2}(a₀ − r^{−2})`, i.e. `r = (a₀ − √t·y)^{−1/2}`, turning

  `∫ Φ((a₀ − r^{−2})/√t)·r^{n−1} dr`   into   `(√t/2)·∫ Φ(y)·(a₀ − √t·y)^{−(n+2)/2} dy`.

The Mathlib entry point is **`MeasureTheory.integral_image_eq_integral_abs_deriv_smul`**
(`Function/JacobianOneDim.lean:66`), *not* `intervalIntegral.integral_comp_smul_deriv`: the latter
demands `Continuous g` **globally**, which is false here — `Phi` is discontinuous at `0` (Lean's
`1/0 = 0` makes `Phi 0 = 0` rather than `1/2`) and `r ↦ r^{−2}` is discontinuous at `0`.  The
Jacobian version asks only for `MeasurableSet s`, `HasDerivWithinAt` on `s`, and `InjOn`, so the
discontinuities never have to be dealt with. -/

section Substitution

/-- The substitution `y ↦ r = (a₀ − s·y)^{−1/2}`, with `s = √t`. -/
noncomputable def subst (a₀ s y : ℝ) : ℝ := (Real.sqrt (a₀ - s * y))⁻¹

/-- Its derivative, `s / (2·u^{3/2})` with `u = a₀ − s·y`. -/
noncomputable def substDeriv (a₀ s y : ℝ) : ℝ :=
  s / (2 * (a₀ - s * y) * Real.sqrt (a₀ - s * y))

theorem hasDerivAt_subst {a₀ s y : ℝ} (hu : 0 < a₀ - s * y) :
    HasDerivAt (subst a₀ s) (substDeriv a₀ s y) y := by
  have hune : a₀ - s * y ≠ 0 := ne_of_gt hu
  have hsq0 : (0 : ℝ) < Real.sqrt (a₀ - s * y) := Real.sqrt_pos.2 hu
  have hlin : HasDerivAt (fun z : ℝ => a₀ - s * z) (-s) y := by
    have h1 : HasDerivAt (fun z : ℝ => s * z) s y := by
      simpa using (hasDerivAt_id y).const_mul s
    simpa using h1.const_sub a₀
  have hsqrt : HasDerivAt (fun z : ℝ => Real.sqrt (a₀ - s * z))
      (1 / (2 * Real.sqrt (a₀ - s * y)) * (-s)) y :=
    (Real.hasDerivAt_sqrt hune).comp y hlin
  have hinv := hsqrt.inv (ne_of_gt hsq0)
  have heq : -(1 / (2 * Real.sqrt (a₀ - s * y)) * (-s)) / Real.sqrt (a₀ - s * y) ^ 2
      = substDeriv a₀ s y := by
    rw [substDeriv, Real.sq_sqrt hu.le]
    field_simp
  rwa [heq] at hinv

/-- `(a₀ − s·y) = 1/(subst a₀ s y)²`: the substitution inverts `r ↦ (a₀ − r^{−2})/s`. -/
theorem subst_sq {a₀ s y : ℝ} (hu : 0 < a₀ - s * y) :
    (subst a₀ s y) ^ 2 = (a₀ - s * y)⁻¹ := by
  rw [subst, inv_pow, Real.sq_sqrt hu.le]

theorem subst_pos {a₀ s y : ℝ} (hu : 0 < a₀ - s * y) : 0 < subst a₀ s y := by
  rw [subst]
  exact inv_pos.2 (Real.sqrt_pos.2 hu)

/-- The substitution is strictly increasing where it is defined (`s > 0`). -/
theorem strictMonoOn_subst {a₀ s : ℝ} (hs : 0 < s) {S : Set ℝ}
    (hS : ∀ y ∈ S, 0 < a₀ - s * y) : StrictMonoOn (subst a₀ s) S := by
  intro y hy z hz hyz
  have huy := hS y hy
  have huz := hS z hz
  have hlt : a₀ - s * z < a₀ - s * y := by nlinarith
  have hkey : Real.sqrt (a₀ - s * z) < Real.sqrt (a₀ - s * y) :=
    Real.sqrt_lt_sqrt huz.le hlt
  rw [subst, subst, inv_lt_inv₀ (Real.sqrt_pos.2 huy) (Real.sqrt_pos.2 huz)]
  exact hkey

theorem injOn_subst {a₀ s : ℝ} (hs : 0 < s) {S : Set ℝ}
    (hS : ∀ y ∈ S, 0 < a₀ - s * y) : Set.InjOn (subst a₀ s) S :=
  (strictMonoOn_subst hs hS).injOn

/-- **The change of variables.**  With `S` the `y`-window and `subst '' S` the corresponding
`r`-shell, the radial integral becomes the `y`-integral.  No continuity of the integrand is
required. -/
theorem integral_subst_image {a₀ s : ℝ} (hs : 0 < s) {S : Set ℝ} (hSm : MeasurableSet S)
    (hS : ∀ y ∈ S, 0 < a₀ - s * y) (G : ℝ → ℝ) :
    ∫ r in subst a₀ s '' S, G r
      = ∫ y in S, |substDeriv a₀ s y| * G (subst a₀ s y) := by
  have hderiv : ∀ y ∈ S, HasDerivWithinAt (subst a₀ s) (substDeriv a₀ s y) S y :=
    fun y hy => (hasDerivAt_subst (hS y hy)).hasDerivWithinAt
  simpa [smul_eq_mul] using
    MeasureTheory.integral_image_eq_integral_abs_deriv_smul hSm hderiv (injOn_subst hs hS) G

/-- **The substituted integrand.**  `|φ'(y)|·φ(y)^{n−1} = (s/2)·(a₀ − s·y)^{−(n+2)/2}` — the
exponent `(n+2)/2` of eq. (56), assembled from `r^{n−1}` and the Jacobian's `u^{−3/2}`. -/
theorem subst_integrand {a₀ s y : ℝ} (hu : 0 < a₀ - s * y) (hs : 0 ≤ s) {n : ℕ} (hn : 1 ≤ n) :
    |substDeriv a₀ s y| * (subst a₀ s y) ^ (n - 1)
      = s / 2 * (a₀ - s * y) ^ (-(((n : ℝ) + 2) / 2)) := by
  have hu0 : (0 : ℝ) < a₀ - s * y := hu
  have hsq0 : (0 : ℝ) < Real.sqrt (a₀ - s * y) := Real.sqrt_pos.2 hu0
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have : (1 : ℕ) ≤ n := hn
    push_cast [Nat.cast_sub this]
    ring
  -- the Jacobian is nonnegative, so the absolute value disappears
  have habs : |substDeriv a₀ s y| = s / (2 * (a₀ - s * y) * Real.sqrt (a₀ - s * y)) := by
    rw [substDeriv, abs_of_nonneg]
    positivity
  -- rewrite `subst` and `√` as `rpow`
  have hsqrt : Real.sqrt (a₀ - s * y) = (a₀ - s * y) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
  have hsubst : subst a₀ s y = (a₀ - s * y) ^ (-((1 : ℝ) / 2)) := by
    rw [subst, hsqrt, ← Real.rpow_neg hu0.le]
  have hpow : (subst a₀ s y) ^ (n - 1)
      = (a₀ - s * y) ^ (-((1 : ℝ) / 2) * ((n : ℝ) - 1)) := by
    rw [hsubst, ← Real.rpow_natCast ((a₀ - s * y) ^ (-((1 : ℝ) / 2))) (n - 1),
      ← Real.rpow_mul hu0.le, hcast]
  have hmul : (a₀ - s * y) ^ ((3 : ℝ) / 2)
      = (a₀ - s * y) * Real.sqrt (a₀ - s * y) := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hu0, Real.rpow_one, ← hsqrt]
  have hne : (a₀ - s * y) * Real.sqrt (a₀ - s * y) ≠ 0 := by positivity
  have hjac : s / (2 * (a₀ - s * y) * Real.sqrt (a₀ - s * y))
      = s / 2 * (a₀ - s * y) ^ (-((3 : ℝ) / 2)) := by
    rw [Real.rpow_neg hu0.le, hmul]
    field_simp
  rw [habs, hpow, hjac, mul_assoc, ← Real.rpow_add hu0]
  congr 2
  ring

/-- **The `a₀ ≥ 1` normalisation** (p. 20): `(a₀ − u)^{−c} ≤ (1 − u)^{−c}`, which is how the
substituted integrand `(a₀ − s·y)^{−(n+2)/2}` is handed to `Lemma43.integrand_le`, whose statement
is normalised at `a₀ = 1`.  The paper writes this as `a₀^{−(n+2)/2} ≤ 1`. -/
theorem rpow_neg_le_of_one_le {a₀ u c : ℝ} (ha : 1 ≤ a₀) (hu : 0 < 1 - u) (hc : 0 ≤ c) :
    (a₀ - u) ^ (-c) ≤ (1 - u) ^ (-c) := by
  have h2 : 1 - u ≤ a₀ - u := by linarith
  have ha0 : (0 : ℝ) < a₀ - u := by linarith
  have h3 : (1 - u) ^ c ≤ (a₀ - u) ^ c := Real.rpow_le_rpow hu.le h2 hc
  have h4 : (0 : ℝ) < (1 - u) ^ c := Real.rpow_pos_of_pos hu c
  have h5 : (0 : ℝ) < (a₀ - u) ^ c := Real.rpow_pos_of_pos ha0 c
  rw [Real.rpow_neg ha0.le, Real.rpow_neg hu.le, inv_le_inv₀ h5 h4]
  exact h3

/-! ### How the pieces compose

For the record, the chain from the radial integral to `ChainData.weight_bound`:

1. `integral_subst_image` turns `∫_{shell} Φ((a₀−r⁻²)/√t)·r^{n−1} dr` into
   `∫_{window} |φ'(y)|·Φ(y)·φ(y)^{n−1} dy`;
2. `subst_integrand` evaluates the Jacobian factor as `(√t/2)·(a₀ − √t·y)^{−(n+2)/2}`;
3. `rpow_neg_le_of_one_le` normalises `a₀` away, giving `(1 − √t·y)^{−(n+2)/2}`;
4. `Lemma43.integrand_le` factors out `e^{n²t/8}` — **the load-bearing `1/8`** — leaving a shifted
   Gaussian over `y`;
5. `gaussian_over_y_le` bounds that by `(2 + 2√(2π))/b`, `b = n√t/2`;
6. `Lemma43.prefactor_cancel` cancels the prefactor `b`, leaving an absolute constant;
7. `dom_of_antitone` supplies `hdom` at the cube's worst point;
8. `Lemma43.lintegral_radial_le` and `weight_bound_of_params` deliver `ChainData.weight_bound`.

Steps 1-3 and 5-8 are proved here or in `Lemma43.lean`; step 4 is `Lemma43.integrand_le`.  What is
**not** assembled into a single end-to-end theorem is the bookkeeping that identifies the window
`S` with `(0, C₀√n]`, the shell `subst '' S` with the support of the chain's profile, and the
three-piece split `I₁ + I₂ + I₃` — see report 10 §5. -/

end Substitution

end Submission.L10

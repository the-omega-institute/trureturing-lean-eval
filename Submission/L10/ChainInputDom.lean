/-
Gate L-10 (`klartag_packing`), brief 37.

**`ChainInput.dom` from the per-point tail.**

`Params.dom` asks for the contact weight to sit below the radial profile at *every point of the
cube around the lattice point*, not at the lattice point itself.  `Profile.profile` already carries
the inward shift `r ↦ α·(r − √n/2)`, so the link is one application of `Lemma43B.dom_of_antitone`
to the `t`-integrated profile — §1.

§2 identifies `Padding.padded_tail_of_increments`' `Φ(M₀/(√t·q))` with `profile` at the same time,
so the per-point tail and the profile are the same function of the radius.

§4 records the obstruction that decides the architecture, and §5 packages everything the discharge
must supply as one structure.
-/
import Submission.L10.Lemma43Uniform
import Submission.L10.Padding

namespace Submission.L10

open MeasureTheory Set Real Submission.L10.ChainDataInst Submission.L10.Tiling
open Submission.L10.Section5 Submission.L10.ConstructionA
open scoped ENNReal NNReal

/-! ## 1. The worst point of the cube -/

/-- The un-widened profile: `profile` evaluated at the lattice point's own radius.  `profile`'s
argument is already shifted inward by `√n/2`, so undoing that shift is adding `√n/2`. -/
noncomputable def profileAt (a₀ α W : ℝ) (n : ℕ) (t r : ℝ) : ℝ :=
  profile a₀ α W n t (r + Real.sqrt n / 2)

theorem profileAt_antitone {a₀ α W : ℝ} {n : ℕ} {t : ℝ} (hα : 0 < α) (ht : 0 < t) :
    Antitone (profileAt a₀ α W n t) := by
  intro r₁ r₂ h
  show profile a₀ α W n t (r₂ + Real.sqrt n / 2) ≤ profile a₀ α W n t (r₁ + Real.sqrt n / 2)
  exact profile_antitone hα ht (by linarith)

/-- **`ChainInput.dom` from a bound at the lattice point itself.**  `dom_of_antitone` widens the
`t`-integrated profile to the cube's worst point; the shift in `profileAt` is exactly the cube
radius `√n/2` that `Tiling.norm_le_of_mem_cube` costs. -/
theorem dom_of_tail {n : ℕ} (hn : 0 < n) {a₀ α W T : ℝ} (hα : 0 < α)
    (w : (Fin n → ℤ) → ℝ≥0∞) (supp : Finset (Fin n → ℤ))
    (htail : ∀ y ∈ supp, w y ≤ ENNReal.ofReal
      (∫ t in Ioc (0 : ℝ) T, profileAt a₀ α W n t ‖toE n y‖)) :
    ∀ y ∈ supp, ∀ x ∈ cube (toE n y),
      w y ≤ ENNReal.ofReal (∫ t in Ioc (0 : ℝ) T, profile a₀ α W n t ‖x‖) := by
  intro y hy x hx
  have hanti : Antitone (fun r : ℝ => ∫ t in Ioc (0 : ℝ) T, profileAt a₀ α W n t r) :=
    antitone_integral (fun t ht => profileAt_antitone hα ht.1)
      (fun r => integrableOn_profile_time (r + Real.sqrt n / 2))
  have hwide := dom_of_antitone hn hanti supp y hy x hx
  have heq : (∫ t in Ioc (0 : ℝ) T, profileAt a₀ α W n t (‖x‖ - Real.sqrt n / 2))
      = ∫ t in Ioc (0 : ℝ) T, profile a₀ α W n t ‖x‖ := by
    simp [profileAt, sub_add_cancel]
  rw [heq] at hwide
  exact le_trans (htail y hy) hwide

/-! ## 2. The per-point tail and the profile are the same function

`Padding.padded_tail_of_increments` bounds the hitting probability by `4·Φ(M₀/(√t·q))`.  With
Klartag's `M₀ = a₀ − (α·r)⁻²` and `q = 1` — eq. (61) read at the scaled radius — that argument is
`yOf a₀ t (α·r)`, and `Φ` at it is `profileAt` away from the two caps. -/

theorem profileAt_eq_Phi {a₀ α W : ℝ} {n : ℕ} {t r : ℝ}
    (hW : r + Real.sqrt n / 2 ≤ W) (hr : 0 < α * r)
    (hy : 0 < yOf a₀ t (α * r)) :
    profileAt a₀ α W n t r = Phi (yOf a₀ t (α * r)) := by
  have hadd : r + Real.sqrt n / 2 - Real.sqrt n / 2 = r := by ring
  unfold profileAt profile
  rw [ite_eq_right (not_lt.2 hW), hadd, ite_eq_right (not_le.2 hr), PhiC_of_pos hy]

/-! ## 3. What the discharge must supply -/

/-- **The chain's raw parameters.**  `ChainInput` with `dom` replaced by `tail`: the per-point
bound at the lattice point's own radius, which is what `Padding.padded_tail_of_increments`
produces (through the `stepGood`/`wiredGood` stack) once the `4` of report 2 §5.2 is absorbed
into `w`. -/
structure ChainRaw (p n : ℕ) where
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
  /-- **The only probabilistic input.**  Proposition 4.1 at each horizon `t`, at the lattice
  point's own radius. -/
  tail : ∀ y ∈ supp, w y ≤ ENNReal.ofReal
    (∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
      profileAt (a0C n) alpha (windowC alpha n) n t ‖toE n y‖)
  arith : (n : ℝ) * kappa n * ((p : ℝ) - 1) * (8 - 8 / (n : ℝ) ^ 2) < 8 * ((p : ℝ) ^ n - 1)

/-- **`ChainInput` from the chain's raw parameters** — `dom` discharged by §1. -/
def chainInput_of_params {p n : ℕ} (hn : 0 < n) (Q : ChainRaw p n) : ChainInput p n where
  alpha := Q.alpha
  alpha_pos := Q.alpha_pos
  alpha_norm := Q.alpha_norm
  R := Q.R
  R_nonneg := Q.R_nonneg
  R_scaled := Q.R_scaled
  R_lt_p := Q.R_lt_p
  tiling_defect := Q.tiling_defect
  window_lt_p := Q.window_lt_p
  w := Q.w
  supp := Q.supp
  supp_ne_zero := Q.supp_ne_zero
  supp_radius := Q.supp_radius
  dom := dom_of_tail hn Q.alpha_pos Q.w Q.supp Q.tail
  arith := Q.arith

/-- `Params` from the chain's raw parameters. -/
noncomputable def params_of_raw {p n : ℕ} [Fact (Nat.Prime p)] (hn : 2073600 ≤ n)
    (Q : ChainRaw p n) : Params p n :=
  params_of_chain hn (chainInput_of_params (by omega) Q)

/-- **The hand-off.**  `Threshold2.remaining_of_lemma43` fed from `ChainRaw` alone.  Beyond the
chain's parameter definitions the only input is `ChainRaw.tail`. -/
theorem lemma43_input_of_raw {c₀ : ℝ} (hc₀ : 0 < c₀)
    (H : ∀ m : ℕ, Threshold2.n₁ ≤ m →
      ∃ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p) (Q : ChainRaw p (m + 1)),
        ∀ g : Fin (m + 1) → ZMod p, g ≠ 0 →
          (∀ y : Fin (m + 1) → ℤ, y ≠ 0 → ‖toE (m + 1) y‖ ≤ Q.R → y ∉ latZ p (m + 1) g) →
          Assembly.ChainOutput Q.alpha g c₀) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      let V := EuclideanSpace ℝ (Fin (n + 1))
      ∃ φ : V →ₗ[ℝ] V, let E := φ '' Metric.ball (0 : V) 1
        (MeasureTheory.volume E : EReal) = c * n ^ 2 ∧
        {v ∈ E | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} :=
  lemma43_input_of_chain hc₀ (fun m hm => by
    obtain ⟨p, hp, hp0, Q, h⟩ := H m hm
    exact ⟨p, hp, hp0, chainInput_of_params (by omega) Q, h⟩)

/-! ## 4. The obstruction: the `t`-integral cannot dominate a hitting probability

`ChainRaw.tail` is Proposition 4.1 *integrated in `t`*.  If instead the chain's `w` is the
hitting probability over the whole horizon — `padded_tail_of_increments` at `t = T`, which is what
`ChainDataInst.expected_card_le`'s `htail` consumes — then `dom` is unsatisfiable except where the
profile vanishes: `profile` is monotone in `t` (report 35), so its `t`-integral is at most
`T·profile(T,·)`, and `T = 16·log n/n² < 4`. -/

theorem integral_le_mul_endpoint {a₀ α W T r : ℝ} {n : ℕ} (hT : 0 ≤ T) :
    (∫ t in Ioc (0 : ℝ) T, profile a₀ α W n t r) ≤ T * profile a₀ α W n T r := by
  have hconst : IntegrableOn (fun _ : ℝ => profile a₀ α W n T r) (Ioc (0 : ℝ) T) :=
    integrableOn_of_bounded' measurableSet_Ioc (by simp [Real.volume_Ioc])
      aestronglyMeasurable_const (M := ‖profile a₀ α W n T r‖) (fun _ _ => le_rfl)
  have hle : ∫ t in Ioc (0 : ℝ) T, profile a₀ α W n t r
      ≤ ∫ _t in Ioc (0 : ℝ) T, profile a₀ α W n T r :=
    setIntegral_mono_on (integrableOn_profile_time r) hconst measurableSet_Ioc
      (fun t ht => profile_mono_time ht.1 ht.2 r)
  have hvol : (volume.real (Ioc (0 : ℝ) T)) = T := by
    rw [measureReal_def, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal hT]
  rwa [setIntegral_const, hvol, smul_eq_mul] at hle

/-- **The obstruction.**  A hitting-probability weight cannot be dominated by the `t`-integrated
profile unless the profile is zero at the point. -/
theorem hitting_tail_forces_zero {a₀ α W T r : ℝ} {n : ℕ} (hT0 : 0 ≤ T) (hT4 : T < 4)
    (h : 4 * profile a₀ α W n T r ≤ ∫ t in Ioc (0 : ℝ) T, profile a₀ α W n t r) :
    profile a₀ α W n T r = 0 := by
  have h1 := integral_le_mul_endpoint (a₀ := a₀) (α := α) (W := W) (n := n) (r := r) hT0
  have h2 : 0 ≤ profile a₀ α W n T r := profile_nonneg _ _
  nlinarith

/-- `T = 16·log n/n² < 4` at the chain's threshold, so the obstruction is live. -/
theorem horizon_lt_four {n : ℕ} (hn : 2073600 ≤ n) : ChainDrift.horizon n < 4 := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hlogle : Real.log n ≤ (n : ℝ) - 1 := Real.log_le_sub_one_of_pos hnpos
  rw [horizon_eq, div_lt_iff₀ (by positivity)]
  nlinarith

end Submission.L10

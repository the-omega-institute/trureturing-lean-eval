/-
Gate L-10 (`klartag_packing`), brief 33.

**`Params''` and `weight_bound_of_params''`.**

Report 32 found that `Params'.f_eq` pins Lemma 4.3's profile at the *single* time `T`, while
`Lemma43C.weight_bound_of_chain` consumes the profile integrated over `t ∈ (0,T]`.  `Params''`
is the successor that fixes this: `f_eq'` replaces `f_eq` (which stays on `toParams'`, vestigial),
and `toParams` is untouched, so briefs 13, 17 and 25's interfaces stand unchanged —
`chainData_of_params''` is `chainData_of_params ∘ toParams`.

Three groups of new fields:

* **the fix** — `f_eq'`;
* **bookkeeping** — `C1`, `C1_nonneg`, `C_eq`, normalising `Params.C` into the shape
  `Lemma43D.markov_of_arith` produces and `weight_bound_of_chain` consumes;
* **the one remaining obligation** — `hgbound'`, Lemma 4.3 *uniformly in `t`*.  See §4.

`hyint'` is **not** a field: it is proved here (`integrableOn_profile_radial_t`).
-/
import Submission.L10.Lemma43Close
import Submission.L10.Threshold2

namespace Submission.L10

open MeasureTheory Set Real Submission.L10.ChainDataInst Submission.L10.Tiling
open Submission.L10.Section5 Submission.L10.ConstructionA
open scoped ENNReal NNReal

/-! ## 1. The radial integrability of the `t`-integrated profile

`weight_bound_of_chain`'s `hyint`, at the concrete profile.  The `t`-integral is bounded by `T/2`
(`Φ ≤ 1/2`), vanishes past the window, and is strongly measurable by Fubini's measurability
lemma — so `Lemma43D.integrableOn_Ioi_of_support` applies exactly as it does at fixed `t`. -/

theorem integrableOn_profile_radial_t {a₀ α W T : ℝ} {n : ℕ} (hW : 0 ≤ W) (hT : 0 ≤ T) :
    IntegrableOn (fun y : ℝ => y ^ (n - 1) * ∫ t in Ioc (0 : ℝ) T, profile a₀ α W n t y)
      (Ioi (0 : ℝ)) := by
  have hsm : StronglyMeasurable (fun y : ℝ => ∫ t in Ioc (0 : ℝ) T, profile a₀ α W n t y) :=
    ((measurable_profile_uncurry (a₀ := a₀) (α := α) (W := W) (n := n)).comp
      measurable_swap).stronglyMeasurable.integral_prod_right'
  have hbnd : ∀ y : ℝ, ‖∫ t in Ioc (0 : ℝ) T, profile a₀ α W n t y‖ ≤ 1 / 2 * T := by
    intro y
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0 : ℝ) T)
      (C := 1 / 2) (f := fun t => profile a₀ α W n t y)
      (by simp [Real.volume_Ioc]) (fun t _ => norm_profile_le t y)
    simpa [Real.volume_Ioc, max_eq_left hT] using h
  refine integrableOn_Ioi_of_support hW ?_ ?_
  · refine integrableOn_of_bounded' measurableSet_Ioc (by simp [Real.volume_Ioc])
      (((measurable_id.pow_const (n - 1)).stronglyMeasurable.mul hsm).aestronglyMeasurable)
      (M := W ^ (n - 1) * (1 / 2 * T)) ?_
    intro y hy
    have hy0 : (0 : ℝ) ≤ y := hy.1.le
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hy0 _)]
    exact mul_le_mul (pow_le_pow_left₀ hy0 hy.2 _) (hbnd y) (norm_nonneg _)
      (pow_nonneg (le_trans hy0 hy.2) _)
  · intro y hy
    simp [profile_zero_of_gt hy]

/-! ## 2. `Params''` -/

/-- **`Params'` with `f` pinned to the `t`-integrated profile.**  `f_eq` on `toParams'` is now
vestigial; nothing below reads it. -/
structure Params'' (p n : ℕ) extends Params' p n where
  /-- Report 32's fix: `f` is the profile integrated over `t ∈ (0,T]`, not the profile at `T`. -/
  f_eq' : f = fun r => ∫ t in Ioc (0 : ℝ) T, profile a0 alpha windowRadius n t r
  /-- Lemma 4.3's **per-`t`** constant, `ρⁿ/(2n) + e^{1/2}K/(n·αⁿ)` in report 31's notation. -/
  C1 : ℝ
  C1_nonneg : 0 ≤ C1
  /-- `Params.C` normalised: `∫₀ᵀ e^{n²t/8} dt = 8 − 8/n²` exactly
  (`Lemma43C.integral_exp_n2_eq`), and this is the shape `Lemma43D.markov_of_arith` produces. -/
  C_eq : C = C1 * (8 - 8 / (n : ℝ) ^ 2)
  /-- **The one remaining obligation** — Lemma 4.3 uniformly in `t`; see §4. -/
  hgbound' : ∀ t ∈ Ioc (0 : ℝ) T,
    ∫⁻ y in Ioi (0 : ℝ),
        ENNReal.ofReal (y ^ (n - 1) * profile a0 alpha windowRadius n t y)
      ≤ ENNReal.ofReal (C1 * Real.exp ((n : ℝ) ^ 2 / 8 * t))

/-! ## 3. Lemma 4.3, discharged at `Params''` -/

/-- **`Section5.ChainData.weight_bound` from `Params''`** — the field `chainData_of_params`
consumes.  Every hypothesis of `Lemma43C.weight_bound_of_chain` comes from a field of `Params''`
or from a lemma of `Profile`/`Lemma43D`; the only numeric input is `n ≥ 2 073 600`. -/
theorem weight_bound_of_params'' {p n : ℕ} [Fact (Nat.Prime p)] (P : Params'' p n)
    (hn : 2073600 ≤ n) :
    2 * (((p - 1 : ℕ) : ℝ≥0∞) * ∑ y ∈ P.supp, P.w y)
      < P.theta * ((p ^ n - 1 : ℕ) : ℝ≥0∞) := by
  have hn0 : 0 < n := by omega
  have hT : P.T = 16 * Real.log n / (n : ℝ) ^ 2 := by rw [P.T_eq]; rfl
  have hmeas : AEMeasurable
      (Function.uncurry (fun y t : ℝ =>
        ENNReal.ofReal (y ^ (n - 1) * profile P.a0 P.alpha P.windowRadius n t y)))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioc (0 : ℝ) P.T))) :=
    (((measurable_fst.pow_const (n - 1)).mul
      (measurable_profile_uncurry.comp measurable_swap)).ennreal_ofReal).aemeasurable
  have hdom : ∀ y ∈ P.supp, ∀ x ∈ cube (toE n y),
      P.w y ≤ ENNReal.ofReal
        (∫ t in Ioc (0 : ℝ) P.T, profile P.a0 P.alpha P.windowRadius n t ‖x‖) := by
    intro y hy x hx
    have h := P.dom y hy x hx
    rwa [P.f_eq'] at h
  have hxint : Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      ∫ t in Ioc (0 : ℝ) P.T, profile P.a0 P.alpha P.windowRadius n t ‖x‖) := by
    have h := P.integrable
    rwa [P.f_eq'] at h
  have hlogn : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hTpos : 0 < P.T := by rw [hT]; positivity
  have hW : 0 ≤ P.windowRadius :=
    le_trans P.radius_nonneg (P.radius_le hTpos le_rfl P.Y_nonneg)
  have hmarkov : 2 * (((p - 1 : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal ((n : ℝ) * kappa n * (P.C1 * (8 - 8 / (n : ℝ) ^ 2))))
      < P.theta * ((p ^ n - 1 : ℕ) : ℝ≥0∞) := by
    have h := P.markov
    rwa [P.C_eq] at h
  exact weight_bound_of_chain hn0 hT P.C1_nonneg
    (fun t r => profile_nonneg t r) (fun r => integrableOn_profile_time r)
    hmeas P.hgbound' P.w P.supp hdom hxint
    (integrableOn_profile_radial_t hW hTpos.le) P.theta hmarkov

/-- `Section5.ChainData` from `Params''` — `chainData_of_params ∘ toParams`. -/
def chainData_of_params'' {p n : ℕ} [Fact (Nat.Prime p)] [NeZero p] (P : Params'' p n) :
    ChainData p n :=
  chainData_of_params P.toParams

/-- §5's line `g`, from `Params''`. -/
theorem exists_good_line_of_params'' {p n : ℕ} [Fact (Nat.Prime p)] [NeZero p]
    (P : Params'' p n) :
    ∃ g : Fin n → ZMod p, g ≠ 0 ∧
      (∀ y : Fin n → ℤ, y ≠ 0 → ‖toE n y‖ ≤ P.R → y ∉ latZ p n g) ∧
      ∑ y ∈ P.supp.filter (fun y => y ∈ latZ p n g), P.w y < P.theta :=
  exists_good_line_of_params P.toParams

/-! ## 4. What the discharge must supply -/

/-- **`lemma43_input`.**  `Threshold2.remaining_of_lemma43` quantifies over `Params`, and
`Params''.toParams` *is* that `Params`; `R` and `alpha` are inherited definitionally.  So this is
the exact statement the chain's discharge must supply, with `Params` replaced by `Params''`. -/
theorem lemma43_input {c₀ : ℝ} (hc₀ : 0 < c₀)
    (H : ∀ m : ℕ, Threshold2.n₁ ≤ m →
      ∃ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p) (P : Params'' p (m + 1)),
        ∀ g : Fin (m + 1) → ZMod p, g ≠ 0 →
          (∀ y : Fin (m + 1) → ℤ, y ≠ 0 → ‖toE (m + 1) y‖ ≤ P.R → y ∉ latZ p (m + 1) g) →
          Assembly.ChainOutput P.alpha g c₀) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      let V := EuclideanSpace ℝ (Fin (n + 1))
      ∃ φ : V →ₗ[ℝ] V, let E := φ '' Metric.ball (0 : V) 1
        (MeasureTheory.volume E : EReal) = c * n ^ 2 ∧
        {v ∈ E | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} :=
  Threshold2.remaining_of_lemma43 hc₀ (fun m hm => by
    obtain ⟨p, hp, hp0, P, h⟩ := H m hm
    exact ⟨p, hp, hp0, P.toParams, h⟩)

end Submission.L10

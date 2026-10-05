import Submission.L10.TailAtStepR4W2
import Submission.L10.TerminalCount
import Submission.L10.ChainWalkRW2
import Submission.L10.Lemma43UniformR3
import Submission.L10.GoodPathLightR2

/-!
# Gate L-10 (`klartag_packing`), brief 85f — `ChainRaw3`: the raw datum with a terminal weight

Report 74 §4's combined weight needs a **second** bound on the raw datum: the terminal contact
probability at the last step, which `ChainRaw2RW2.tail` (the time-integrated bound) does not carry.
`ChainRaw3` adds it as a field and `chainRaw3_of_walk` supplies it from the chain, by
`TerminalCount.terminal_tail_of_hsteps` at `k = N − 1` on top of `hsteps_of_walkRW2` — the same
inputs `chainRaw2_of_walkRW2` already takes, with no new hypothesis.

The field is stated at `t = ChainDrift.horizon n` rather than at `(N−1)·h`, because that is where
`Lemma43R2.radial_bound_terminal2` lives; the bump is `profile`'s monotonicity in `t`
(`profile_mono_time`), discharged in the constructor.

§§2-5 fold the combined weight in.  `params_of_raw3` is `TailAtStepR2W2.params_of_raw2R_of_radial`
with six fields changed (report 74 §4): `w := A·w_int + B·w_T`, `f := A·f_int + 4B·f_T`, `dom`,
`integrable`, `C` and `radial_bound`, the last by brief 85e's `Lemma43R3.radial_bound_combined_le`.
`theta` and `markov` are untouched, because `markov_tight` reads only `C`.

**Route note, 2026-09-12.**  `Theorem2R3.wR2` is the `intWeight` of the chain run on `shellR`,
while the drift side runs its chain on `windowOfR2` — different processes, since `Chain.lift` reads
the violated constraints of the set it is run on.  So the §5 weight here is the **profile bound
itself** (`wProf`, `wProfT`): `g`-free, chain-free, both tail fields `le_refl`, and §8 transfers it
to whatever `W'` the drift side runs on, in the only direction §5 needs.

§6 is `TerminalCount.sums_of_combined` at `DriftStopped8R5.windowOfR2`, and §7 is the closing line:
85d's hypothesis-free producer is exactly `Theorem2R3.ParamsProducerR2` at `thetaR2`, so 85c's
bridge takes it with nothing left on the tail side.
-/

set_option linter.unusedSectionVars false

namespace Submission.L10.TailAtStepR5W2

open MeasureTheory Set Real Finset
open scoped ENNReal NNReal RealInnerProductSpace
open Submission.L10 Submission.L10.Increments Submission.L10.ChainDataInst
open Submission.L10.Tiling Submission.L10.Section5 Submission.L10.ConstructionA
open Submission.L10.WindowR2 Submission.L10.Chain

noncomputable section

variable {n : ℕ}

/-- **The raw datum with a terminal weight.**  `ChainRaw2RW2` plus the single-time bound the
count event needs. -/
structure ChainRaw3 (p n : ℕ) extends ChainRaw2RW2 p n where
  /-- The terminal contact weight. -/
  wT : (Fin n → ℤ) → ℝ≥0∞
  /-- Its bound, at the horizon: the second summand of report 74 §4's combined weight. -/
  tailT : ∀ y ∈ toChainRaw2RW2.supp, wT y ≤ ENNReal.ofReal
    (4 * profileAt (a0C n) toChainRaw2RW2.alpha
      (windowR2 toChainRaw2RW2.alpha n) n (ChainDrift.horizon n) ‖toE n y‖)

/-- The terminal step's bound is below the horizon's, by monotonicity of `profile` in `t`. -/
theorem profStep_le_horizon {α : ℝ} (hn : 3 ≤ n) {K : ℕ} (y : Fin n → ℤ)
    (hK : (K : ℝ) * ParamsAdopted2.stepSizeAdopted2 n ≤ ChainDrift.horizon n) :
    profStepRW2 α n (ParamsAdopted2.stepSizeAdopted2 n) y K
      ≤ profileAt (a0C n) α (windowR2 α n) n (ChainDrift.horizon n) ‖toE n y‖ := by
  by_cases h0 : K = 0
  · simp only [profStepRW2, ite_eq_left h0]
    exact profile_nonneg _ _
  · simp only [profStepRW2, ite_eq_right h0]
    have hKpos : (0 : ℝ) < (K : ℝ) * ParamsAdopted2.stepSizeAdopted2 n := by
      have h1 : (0 : ℝ) < (K : ℝ) := by
        have : 0 < K := Nat.pos_of_ne_zero h0
        exact_mod_cast this
      have h2 : 0 < ParamsAdopted2.stepSizeAdopted2 n :=
        TailSideSetup2.stepSizeAdopted2_pos hn
      positivity
    exact profile_mono_time hKpos hK _

/-! ### The profile weights (route note) -/

/-- The `t`-integrated profile bound, **as** the weight.  `ChainRaw2RW2.tail` at it is `le_refl`. -/
def wProf (α : ℝ) (n : ℕ) : (Fin n → ℤ) → ℝ≥0∞ := fun y =>
  ENNReal.ofReal (4 * ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
    profileAt (a0C n) α (windowR2 α n) n t ‖toE n y‖)

/-- The terminal profile bound, **as** the weight.  `ChainRaw3.tailT` at it is `le_refl`. -/
def wProfT (α : ℝ) (n : ℕ) : (Fin n → ℤ) → ℝ≥0∞ := fun y =>
  ENNReal.ofReal (4 * profileAt (a0C n) α (windowR2 α n) n (ChainDrift.horizon n) ‖toE n y‖)

/-- **The terminal contact bound at `k = N − 1`, pointwise.**  `hsteps_of_walkRW2` at the last
step, bumped to the horizon by `profStep_le_horizon`.  Stated on an arbitrary `W`, so it serves
both `chainRaw3_of_walk` and §8's transfer at the line's window. -/
theorem terminal_le_wProfT {Ωc : Type*} [MeasurableSpace Ωc] {P : Measure Ωc}
    [IsProbabilityMeasure P] {Ec : Type*} [NormedAddCommGroup Ec] [InnerProductSpace ℝ Ec]
    [FiniteDimensional ℝ Ec] {q : (Fin n → ℤ) → Ec} {W : Finset (Fin n → ℤ)} {A₀ : Ec}
    {ξ : ℕ → Ωc → Ec} {α : ℝ} (hn : 3 ≤ n)
    (hq : ∀ j : (Fin n → ℤ), ∀ i ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫)
    (hA₀ : ∀ y ∈ W, (1 : ℝ) < ⟪A₀, q y⟫)
    (hwin : ∀ y ∈ W, ‖toE n y‖ + Real.sqrt n / 2 ≤ windowR2 α n)
    (hr : ∀ y ∈ W, 0 < α * ‖toE n y‖)
    (hy : ∀ k, k < ParamsAdopted2.numStepsAdopted2 n → k ≠ 0 → ∀ y ∈ W,
      0 < yOf (a0C n) ((k : ℝ) * ParamsAdopted2.stepSizeAdopted2 n) (α * ‖toE n y‖))
    (hprop : ∀ k, k < ParamsAdopted2.numStepsAdopted2 n → k ≠ 0 → ∀ y ∈ W,
      P {ω | ∃ i ≤ k, constraintM q W A₀ ξ y i ω ≤ 0}
        ≤ ENNReal.ofReal (4 * Phi (yOf (a0C n)
            ((k : ℝ) * ParamsAdopted2.stepSizeAdopted2 n) (α * ‖toE n y‖)))) :
    ∀ y ∈ W, ENNReal.ofReal (P.real {ω | y ∈ contactSet q W A₀ ξ
        (ParamsAdopted2.numStepsAdopted2 n - 1) ω}) ≤ wProfT α n y := by
  intro y hy'
  have hNpos : 0 < ParamsAdopted2.numStepsAdopted2 n := by
    have h := ChainDrift.numSteps_pos (n := n) (e := 7) hn
    have : (0 : ℝ) < (ParamsAdopted2.numStepsAdopted2 n : ℕ) := h
    exact_mod_cast this
  have hK : ParamsAdopted2.numStepsAdopted2 n - 1 < ParamsAdopted2.numStepsAdopted2 n := by omega
  have hstep := hsteps_of_walkRW2 (P := P) hq hA₀ hwin hr hy hprop
    (ParamsAdopted2.numStepsAdopted2 n - 1) hK y hy'
  have hh0 : 0 ≤ ParamsAdopted2.stepSizeAdopted2 n :=
    (TailSideSetup2.stepSizeAdopted2_pos hn).le
  have hKle : ((ParamsAdopted2.numStepsAdopted2 n - 1 : ℕ) : ℝ)
      * ParamsAdopted2.stepSizeAdopted2 n ≤ ChainDrift.horizon n := by
    have heq := ParamsAdopted2.numStepsAdopted2_mul_stepSizeAdopted2 hn
    have hle : ((ParamsAdopted2.numStepsAdopted2 n - 1 : ℕ) : ℝ)
        ≤ (ParamsAdopted2.numStepsAdopted2 n : ℝ) := by
      have : (ParamsAdopted2.numStepsAdopted2 n - 1 : ℕ) ≤ ParamsAdopted2.numStepsAdopted2 n := by
        omega
      exact_mod_cast this
    nlinarith [heq, hle, hh0]
  have hbump := profStep_le_horizon (α := α) hn (K := ParamsAdopted2.numStepsAdopted2 n - 1)
    y hKle
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- **`ChainRaw3` from the chain.**  Exactly `chainRaw2_of_walkRW2`'s inputs — no new hypothesis —
with the terminal weight read off `hsteps_of_walkRW2` at `k = N − 1` and bumped to the horizon. -/
def chainRaw3_of_walk {p : ℕ} {Ωc : Type*} [MeasurableSpace Ωc] {P : Measure Ωc}
    [IsProbabilityMeasure P] {Ec : Type*} [NormedAddCommGroup Ec] [InnerProductSpace ℝ Ec]
    [FiniteDimensional ℝ Ec] {q : (Fin n → ℤ) → Ec} {W : Finset (Fin n → ℤ)} {A₀ : Ec}
    {ξ : ℕ → Ωc → Ec} {α : ℝ} (hn : 3 ≤ n)
    (hq : ∀ j : (Fin n → ℤ), ∀ i ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫)
    (hA₀ : ∀ y ∈ W, (1 : ℝ) < ⟪A₀, q y⟫)
    (alpha_pos : 0 < α)
    (alpha_norm : α ^ n * ((p ^ (n - 1) : ℕ) : ℝ) = kappa n)
    (R : ℝ) (R_nonneg : 0 ≤ R) (R_scaled : α * R ≤ 1 - 1 / (n : ℝ)) (R_lt_p : R < (p : ℝ))
    (tiling_defect : (n : ℝ) * (α * Real.sqrt n / 2) ≤ 1 / 4)
    (window_lt_p : windowR2 α n < (p : ℝ))
    (supp_ne_zero : ∀ y ∈ W, y ≠ 0)
    (supp_radius : ∀ y ∈ W, ‖toE n y‖ ≤ windowR2 α n)
    (hwin : ∀ y ∈ W, ‖toE n y‖ + Real.sqrt n / 2 ≤ windowR2 α n)
    (hr : ∀ y ∈ W, 0 < α * ‖toE n y‖)
    (hy : ∀ k, k < ParamsAdopted2.numStepsAdopted2 n → k ≠ 0 → ∀ y ∈ W,
      0 < yOf (a0C n) ((k : ℝ) * ParamsAdopted2.stepSizeAdopted2 n) (α * ‖toE n y‖))
    (hprop : ∀ k, k < ParamsAdopted2.numStepsAdopted2 n → k ≠ 0 → ∀ y ∈ W,
      P {ω | ∃ i ≤ k, constraintM q W A₀ ξ y i ω ≤ 0}
        ≤ ENNReal.ofReal (4 * Phi (yOf (a0C n)
            ((k : ℝ) * ParamsAdopted2.stepSizeAdopted2 n) (α * ‖toE n y‖))))
    (arith : (n : ℝ) * kappa n * ((p : ℝ) - 1) * (8 - 8 / (n : ℝ) ^ 2)
      < 8 * ((p : ℝ) ^ n - 1)) :
    ChainRaw3 p n where
  toChainRaw2RW2 :=
    chainRaw2_of_walkRW2 (P := P) hn hq hA₀ alpha_pos alpha_norm R R_nonneg R_scaled R_lt_p
      tiling_defect window_lt_p supp_ne_zero supp_radius hwin hr hy hprop arith
  wT := fun y => ENNReal.ofReal (P.real
    {ω | y ∈ contactSet q W A₀ ξ (ParamsAdopted2.numStepsAdopted2 n - 1) ω})
  tailT := terminal_le_wProfT hn hq hA₀ hwin hr hy hprop

/-- **The weight swap (route note).**  Any `ChainRaw2RW2` becomes a `ChainRaw3` whose two weights
are the profile bounds themselves: every arithmetic field is carried over untouched and both tail
fields are `le_refl`, so the record is `g`-free and chain-free. -/
def chainRaw3_of_raw2 {p n : ℕ} (Q : ChainRaw2RW2 p n) : ChainRaw3 p n where
  toChainRaw2RW2 := { Q with w := wProf Q.alpha n, tail := fun _y _hy => le_refl _ }
  wT := wProfT Q.alpha n
  tailT := fun _y _hy => le_refl _

/-! ## 2. The two analytic pieces the terminal summand needs

`Params.integrable` and `Params.dom` exist in the tree only for the **`t`-integrated** profile
(`integrable_radial_euclidean`, `dom_of_tail2`).  The terminal summand is a single-time profile, so
both are re-run here; each is the integrated proof with the `t`-integral deleted. -/

/-- **`Params.integrable` for a single-time profile.**  `integrable_radial_euclidean` without the
`t`-integral: bounded by `1/2`, supported in `closedBall 0 W`. -/
theorem integrable_profile_euclidean {a₀ α W T : ℝ} {n : ℕ} :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) => profile a₀ α W n T ‖x‖) := by
  have hsm : StronglyMeasurable (fun x : EuclideanSpace ℝ (Fin n) => profile a₀ α W n T ‖x‖) :=
    (measurable_profile_radius (a₀ := a₀) (α := α) (W := W) (n := n)
      T).stronglyMeasurable.comp_measurable continuous_norm.measurable
  have h1 : IntegrableOn (fun x : EuclideanSpace ℝ (Fin n) => profile a₀ α W n T ‖x‖)
      (Metric.closedBall 0 W) :=
    integrableOn_of_bounded' measurableSet_closedBall (measure_closedBall_lt_top).ne
      hsm.aestronglyMeasurable (M := 1 / 2) (fun x _ => norm_profile_le T ‖x‖)
  have h2 : IntegrableOn (fun x : EuclideanSpace ℝ (Fin n) => profile a₀ α W n T ‖x‖)
      (Metric.closedBall 0 W)ᶜ := by
    refine (integrableOn_zero (μ := volume)
      (s := (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) W)ᶜ)).congr_fun ?_
      measurableSet_closedBall.compl
    intro x hx
    exact (profile_zero_of_gt
      (by simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hx)).symm
  rw [← integrableOn_univ, ← union_compl_self (Metric.closedBall
    (0 : EuclideanSpace ℝ (Fin n)) W)]
  exact h1.union h2

/-- **`Params.dom` for a single-time profile.**  `dom_of_tail2` without the `t`-integral; the
shift in `profileAt` is again exactly the cube radius `√n/2`. -/
theorem dom_of_tailT {n : ℕ} (hn : 0 < n) {a₀ α W T c : ℝ} (hα : 0 < α) (hT : 0 < T) (hc : 0 ≤ c)
    (w : (Fin n → ℤ) → ℝ≥0∞) (supp : Finset (Fin n → ℤ))
    (htail : ∀ y ∈ supp, w y ≤ ENNReal.ofReal (c * profileAt a₀ α W n T ‖toE n y‖)) :
    ∀ y ∈ supp, ∀ x ∈ cube (toE n y),
      w y ≤ ENNReal.ofReal (c * profile a₀ α W n T ‖x‖) := by
  intro y hy x hx
  have hanti : Antitone (fun r : ℝ => c * profileAt a₀ α W n T r) :=
    fun _ _ h => mul_le_mul_of_nonneg_left (profileAt_antitone hα hT h) hc
  have hwide := dom_of_antitone hn hanti supp y hy x hx
  have heq : (c * profileAt a₀ α W n T (‖x‖ - Real.sqrt n / 2))
      = c * profile a₀ α W n T ‖x‖ := by
    simp [profileAt, sub_add_cancel]
  rw [heq] at hwide
  exact le_trans (htail y hy) hwide

/-! ## 3. The combined weight, its profile and its constant (report 74 §4) -/

/-- The combined contact weight: `A·w_int + B·w_T`, in `ℝ≥0∞`. -/
def combW {p n : ℕ} (A B : ℝ) (Q : ChainRaw3 p n) : (Fin n → ℤ) → ℝ≥0∞ :=
  fun y => ENNReal.ofReal A * Q.w y + ENNReal.ofReal B * Q.wT y

/-- Its radial profile.  The `4`s of `ChainRaw3.tail` and `ChainRaw3.tailT` sit inside, so the
second coefficient is `4·B`; that is the `b` of `Lemma43R3.radial_bound_combined_le`. -/
def combF (A B α : ℝ) (n : ℕ) : ℝ → ℝ := fun r =>
  A * (4 * ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
        profile (a0C n) α (windowR2 α n) n t r)
    + 4 * B * profile (a0C n) α (windowR2 α n) n (ChainDrift.horizon n) r

/-- Lemma 4.3's constant for `combF`: the two constants already proved, scaled and added.  **No new
factor of `n` enters** (kill rule 2) — this is 85e §3's right-hand side. -/
def C3 (n : ℕ) (A B α : ℝ) : ℝ :=
  A * (4 * Lemma43R.C1R α n * (8 - 8 / (n : ℝ) ^ 2))
    + 4 * B * (Lemma43R.C1cR (a0C n) α n * (n : ℝ) ^ 2)

theorem C3_pos {n : ℕ} {A B α : ℝ} (hn : 2073600 ≤ n) (hα : 0 < α) (hA : 0 < A) (hB : 0 ≤ B) :
    0 < C3 n A B α := by
  have h1 : 0 < 4 * Lemma43R.C1R α n * (8 - 8 / (n : ℝ) ^ 2) := Lemma43R.C4_pos hn hα
  have h2 : 0 ≤ Lemma43R.C1cR (a0C n) α n := Lemma43R.C1cR_nonneg hα
  have h3 : (0 : ℝ) ≤ 4 * B * (Lemma43R.C1cR (a0C n) α n * (n : ℝ) ^ 2) := by
    have : (0 : ℝ) ≤ Lemma43R.C1cR (a0C n) α n * (n : ℝ) ^ 2 := by positivity
    have h4B : (0 : ℝ) ≤ 4 * B := by linarith
    exact mul_nonneg h4B this
  have h4 : 0 < A * (4 * Lemma43R.C1R α n * (8 - 8 / (n : ℝ) ^ 2)) := mul_pos hA h1
  unfold C3
  linarith

/-- `combF` is nonnegative. -/
theorem combF_nonneg {A B α : ℝ} {n : ℕ} (hA : 0 ≤ A) (hB : 0 ≤ B) (r : ℝ) :
    0 ≤ combF A B α n r := by
  have hI : (0 : ℝ) ≤ ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
      profile (a0C n) α (windowR2 α n) n t r :=
    setIntegral_nonneg measurableSet_Ioc (fun t _ => profile_nonneg t r)
  have hP : (0 : ℝ) ≤ profile (a0C n) α (windowR2 α n) n (ChainDrift.horizon n) r :=
    profile_nonneg _ _
  have h1 : (0 : ℝ) ≤ A * (4 * ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
      profile (a0C n) α (windowR2 α n) n t r) := mul_nonneg hA (by linarith)
  have h2 : (0 : ℝ) ≤ 4 * B * profile (a0C n) α (windowR2 α n) n (ChainDrift.horizon n) r :=
    mul_nonneg (by linarith) hP
  unfold combF
  linarith

/-- The `ℝ≥0∞` arithmetic of `Params.dom` for a sum of two weights, isolated so the record below
does not carry it inline. -/
theorem ofReal_comb_le {A B u v : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hu : 0 ≤ u) (hv : 0 ≤ v)
    {a b : ℝ≥0∞} (ha : a ≤ ENNReal.ofReal (4 * u)) (hb : b ≤ ENNReal.ofReal (4 * v)) :
    ENNReal.ofReal A * a + ENNReal.ofReal B * b
      ≤ ENNReal.ofReal (A * (4 * u) + 4 * B * v) := by
  have h1 : ENNReal.ofReal A * a ≤ ENNReal.ofReal (A * (4 * u)) := by
    rw [ENNReal.ofReal_mul hA]; gcongr
  have h2 : ENNReal.ofReal B * b ≤ ENNReal.ofReal (4 * B * v) := by
    have he : (4 : ℝ) * B * v = B * (4 * v) := by ring
    rw [he, ENNReal.ofReal_mul hB]; gcongr
  have hu4 : (0 : ℝ) ≤ A * (4 * u) := mul_nonneg hA (by linarith)
  have hv4 : (0 : ℝ) ≤ 4 * B * v := mul_nonneg (by linarith) hv
  calc ENNReal.ofReal A * a + ENNReal.ofReal B * b
      ≤ ENNReal.ofReal (A * (4 * u)) + ENNReal.ofReal (4 * B * v) := add_le_add h1 h2
    _ = ENNReal.ofReal (A * (4 * u) + 4 * B * v) := (ENNReal.ofReal_add hu4 hv4).symm

/-! ## 4. `Params` at the combined weight -/

/-- **`params_of_raw3`.**  `TailAtStepR2W2.params_of_raw2R_of_radial` with report 74 §4's six
fields changed and no hypothesis added beyond `0 < A`, `0 ≤ B`: the radial bound is brief 85e's
`radial_bound_combined_le`, whose only side condition is `Q.tiling_defect`, already a field. -/
def params_of_raw3 {p n : ℕ} [Fact (Nat.Prime p)] (hn : 2073600 ≤ n)
    (Q : ChainRaw3 p n) {A B : ℝ} (hA : 0 < A) (hB : 0 ≤ B) : Params p n where
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
  windowRadius := windowR2 Q.alpha n
  window_lt_p := Q.window_lt_p
  f := combF A B Q.alpha n
  f_nonneg := combF_nonneg hA.le hB
  w := combW A B Q
  supp := Q.supp
  supp_ne_zero := Q.supp_ne_zero
  supp_radius := Q.supp_radius
  dom := by
    intro y hy x hx
    have h1 := dom_of_tail2 (n := n) (by omega) Q.alpha_pos (by norm_num : (0 : ℝ) ≤ 4)
      Q.w Q.supp Q.tail y hy x hx
    have h2 := dom_of_tailT (n := n) (by omega) Q.alpha_pos (horizon_pos (by omega))
      (by norm_num : (0 : ℝ) ≤ 4) Q.wT Q.supp Q.tailT y hy x hx
    have hu : (0 : ℝ) ≤ ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
        profile (a0C n) Q.alpha (windowR2 Q.alpha n) n t ‖x‖ :=
      setIntegral_nonneg measurableSet_Ioc (fun t _ => profile_nonneg t _)
    have hv : (0 : ℝ) ≤ profile (a0C n) Q.alpha (windowR2 Q.alpha n) n
        (ChainDrift.horizon n) ‖x‖ := profile_nonneg _ _
    exact ofReal_comb_le hA.le hB hu hv h1 h2
  integrable := by
    have hI := integrable_radial_euclidean (a₀ := a0C n) (α := Q.alpha)
      (W := windowR2 Q.alpha n) (T := ChainDrift.horizon n) (n := n)
      (T_nonneg (by omega : 1 ≤ n))
    have hP := integrable_profile_euclidean (a₀ := a0C n) (α := Q.alpha)
      (W := windowR2 Q.alpha n) (T := ChainDrift.horizon n) (n := n)
    exact ((hI.const_mul 4).const_mul A).add (hP.const_mul (4 * B))
  C := C3 n A B Q.alpha
  radial_bound := by
    simpa only [combF, C3] using
      Lemma43R3.radial_bound_combined_le (α := Q.alpha) (a := A) (b := 4 * B) (n := n)
        hn Q.alpha_pos Q.tiling_defect hA.le (by linarith)
  theta := ENNReal.ofReal (ThetaTight.thetaTight p n (C3 n A B Q.alpha))
  theta_ne_zero := by
    have hC := C3_pos hn Q.alpha_pos hA hB
    have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Nat.Prime.one_lt (Fact.out : Nat.Prime p))
    have hpn : (1 : ℝ) < (p : ℝ) ^ n := one_lt_pow₀ hpR (by omega)
    have hκ : 0 < kappa n := kappa_pos (by omega)
    have hnR : (0 : ℝ) < (n : ℝ) := by
      have : (0 : ℕ) < n := by omega
      exact_mod_cast this
    have hpos : 0 < ThetaTight.thetaTight p n (C3 n A B Q.alpha) := by
      rw [ThetaTight.thetaTight]
      exact div_pos (by positivity) (by linarith)
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    linarith
  theta_ne_top := ENNReal.ofReal_ne_top
  markov :=
    TailAtStepR2W2.markov_tight (n := n) (p := p) (by omega)
      (Nat.Prime.one_lt (Fact.out : Nat.Prime p)) (C3_pos hn Q.alpha_pos hA hB)

/-! ## 5. The producer at the combined family -/

/-- **`paramsProducer3`.**  `Theorem2R3.ParamsProducerR2`'s five equalities, with `ChainRaw3` in
the binder and the combined weight in the fourth — all five are `rfl` on the record above. -/
theorem paramsProducer3 {A B : ℝ} (hA : 0 < A) (hB : 0 ≤ B) :
    ∀ (p m : ℕ) (_ : Fact (Nat.Prime p)), 2073600 ≤ m + 1 → ∀ Q : ChainRaw3 p (m + 1),
      ∃ P : Params p (m + 1), P.alpha = Q.alpha ∧ P.R = Q.R ∧ P.supp = Q.supp ∧
        P.w = combW A B Q ∧
        P.theta = ENNReal.ofReal (ThetaTight.thetaTight p (m + 1) (C3 (m + 1) A B Q.alpha)) := by
  intro p m _hp hm Q
  exact ⟨params_of_raw3 hm Q hA hB, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 6. `sums_of_combined`, instantiated at `windowOfR2` -/

/-- **The split, at a general §5 threshold.**  `TerminalCount.sums_of_combined` asks for
`∑ < 1`; the §5 output is `∑ < θ`, so the coefficients passed to it are divided by `θ`, and the two
admissibility facts become `θ ≤ A·θ₁` and `θ ≤ B·θ₂`.  That pair is scale-invariant in `(A, B)`,
which is why no normalisation of the combined weight is needed. -/
theorem sums_split {ι : Type*} {S : Finset ι} {w₁ w₂ : ι → ℝ≥0∞} {A B : ℝ} {θ θ₁ θ₂ : ℝ≥0∞}
    (hθ0 : θ ≠ 0) (hθt : θ ≠ ⊤)
    (h : ∑ y ∈ S, (ENNReal.ofReal A * w₁ y + ENNReal.ofReal B * w₂ y) < θ)
    (h₁ : θ ≤ ENNReal.ofReal A * θ₁) (h₂ : θ ≤ ENNReal.ofReal B * θ₂) :
    (∑ y ∈ S, w₁ y) < θ₁ ∧ (∑ y ∈ S, w₂ y) < θ₂ := by
  have hinv0 : θ⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 hθt
  have hinvt : θ⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hθ0
  have hcancel : θ⁻¹ * θ = 1 := ENNReal.inv_mul_cancel hθ0 hθt
  refine TerminalCount.sums_of_combined (c₁ := ENNReal.ofReal A * θ⁻¹)
    (c₂ := ENNReal.ofReal B * θ⁻¹) ?_ ?_ ?_
  · have hs : ∑ y ∈ S, (ENNReal.ofReal A * θ⁻¹ * w₁ y + ENNReal.ofReal B * θ⁻¹ * w₂ y)
        = θ⁻¹ * ∑ y ∈ S, (ENNReal.ofReal A * w₁ y + ENNReal.ofReal B * w₂ y) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by ring
    have hlt : (∑ y ∈ S, (ENNReal.ofReal A * w₁ y + ENNReal.ofReal B * w₂ y)) * θ⁻¹
        < θ * θ⁻¹ := ENNReal.mul_lt_mul_left hinv0 hinvt h
    rw [hs]
    calc θ⁻¹ * ∑ y ∈ S, (ENNReal.ofReal A * w₁ y + ENNReal.ofReal B * w₂ y)
        = (∑ y ∈ S, (ENNReal.ofReal A * w₁ y + ENNReal.ofReal B * w₂ y)) * θ⁻¹ := by ring
      _ < θ * θ⁻¹ := hlt
      _ = 1 := ENNReal.mul_inv_cancel hθ0 hθt
  · calc (1 : ℝ≥0∞) = θ⁻¹ * θ := hcancel.symm
      _ ≤ θ⁻¹ * (ENNReal.ofReal A * θ₁) := by gcongr
      _ = ENNReal.ofReal A * θ⁻¹ * θ₁ := by ring
  · calc (1 : ℝ≥0∞) = θ⁻¹ * θ := hcancel.symm
      _ ≤ θ⁻¹ * (ENNReal.ofReal B * θ₂) := by gcongr
      _ = ENNReal.ofReal B * θ⁻¹ * θ₂ := by ring

open Classical in
/-- **The split on the drift side's window.**  One `LightContact` at the combined weight gives the
integrated **and** the terminal light-contact facts on `DriftStopped8R5.windowOfR2` — the second is
the hypothesis report 74 §5 names.  Rule 16: the filter is transported by `filter_eq_windowOfR2`,
never assumed equal. -/
theorem sums_split_windowR2 {p m : ℕ} [NeZero p] {A B : ℝ} (Q : ChainRaw3 p (m + 1))
    {g : Fin (m + 1) → ZMod p} {θ θ₁ θ₂ : ℝ≥0∞}
    (hsupp : Q.supp = RawDataInst2RW2.shellR Q.alpha (m + 1))
    (hθ0 : θ ≠ 0) (hθt : θ ≠ ⊤)
    (h : Theorem2.LightContact (combW A B Q) Q.supp θ g)
    (h₁ : θ ≤ ENNReal.ofReal A * θ₁) (h₂ : θ ≤ ENNReal.ofReal B * θ₂) :
    (∑ y ∈ DriftStopped8R5.windowOfR2 Q.alpha p m g, Q.w y) < θ₁ ∧
      (∑ y ∈ DriftStopped8R5.windowOfR2 Q.alpha p m g, Q.wT y) < θ₂ := by
  have h' := h
  simp only [Theorem2.LightContact, combW, hsupp,
    DriftStopped8R5.filter_eq_windowOfR2] at h'
  exact sums_split hθ0 hθt h' h₁ h₂

/-! ## 7. The closing line -/

/-- 85d's hypothesis-free producer **is** `Theorem2R3.ParamsProducerR2` at the tight family. -/
theorem paramsProducerR2_tight : Theorem2R3.ParamsProducerR2 TailAtStepR4W2.thetaR2 :=
  TailAtStepR4W2.paramsProducerR2'_tight

/-- **The challenge statement from `LightGoodPath2` alone.**  85c's bridge with its `Params`
producer discharged by 85d: on the tail and lattice side nothing remains. -/
theorem klartag_packing_of_lightGoodPath2_tight {c₃ : ℕ → ℝ} (hc₃0 : ∀ n, 0 ≤ c₃ n)
    (hc₃ : ∀ n, c₃ n * DriftStopped6.etaAdopted n ≤ 1 / 4) {C' : ℝ}
    (h : GoodPathLightR2.LightGoodPath2 c₃ Theorem2R3.wR2 TailAtStepR4W2.thetaR2 C') :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      let V := EuclideanSpace ℝ (Fin (n + 1))
      ∃ φ : V →ₗ[ℝ] V, let E := φ '' Metric.ball (0 : V) 1
        (MeasureTheory.volume E : EReal) = c * n ^ 2 ∧
        {v ∈ E | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} :=
  GoodPathLightR2.klartag_packing_of_lightGoodPath2 hc₃0 hc₃ paramsProducerR2_tight h

/-! ## 8. Transfer to the chain the drift side actually runs

`Theorem2R3.wR2` is the `intWeight` of the chain on `shellR`; the drift side's `hS` needs the chain
on `W' := windowOfR2` — a different process, because `Chain.lift` reads the violated constraints of
the set it is run on.  The profile weights of §1 dominate **both**, so one §5 selection at them
serves either chain.  Both lemmas are `Finset.sum_le_sum` over a pointwise bound already in the
tree; neither needs `W' ⊆ shellR`. -/

section Transfer

variable {Ωc : Type*} [MeasurableSpace Ωc] {P : Measure Ωc} [IsProbabilityMeasure P]
variable {Ec : Type*} [NormedAddCommGroup Ec] [InnerProductSpace ℝ Ec] [FiniteDimensional ℝ Ec]
variable {q : (Fin n → ℤ) → Ec} {W : Finset (Fin n → ℤ)} {A₀ : Ec} {ξ : ℕ → Ωc → Ec} {α : ℝ}

/-- **Transfer 1 — the integrated weight.**  `tail_of_transport''RW2` summed: the chain's own
`intWeight`, for the chain run on `W`, is below `wProf` on `W`. -/
theorem sum_intWeight_le_wProf (hn : 3 ≤ n) (hα : 0 < α)
    (hq : ∀ j : (Fin n → ℤ), ∀ i ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫)
    (hA₀ : ∀ y ∈ W, (1 : ℝ) < ⟪A₀, q y⟫)
    (hwin : ∀ y ∈ W, ‖toE n y‖ + Real.sqrt n / 2 ≤ windowR2 α n)
    (hr : ∀ y ∈ W, 0 < α * ‖toE n y‖)
    (hy : ∀ k, k < ParamsAdopted2.numStepsAdopted2 n → k ≠ 0 → ∀ y ∈ W,
      0 < yOf (a0C n) ((k : ℝ) * ParamsAdopted2.stepSizeAdopted2 n) (α * ‖toE n y‖))
    (hprop : ∀ k, k < ParamsAdopted2.numStepsAdopted2 n → k ≠ 0 → ∀ y ∈ W,
      P {ω | ∃ i ≤ k, constraintM q W A₀ ξ y i ω ≤ 0}
        ≤ ENNReal.ofReal (4 * Phi (yOf (a0C n)
            ((k : ℝ) * ParamsAdopted2.stepSizeAdopted2 n) (α * ‖toE n y‖)))) :
    ∑ y ∈ W, ENNReal.ofReal (ContactIntegrated.intWeight P (contactSet q W A₀ ξ)
        (ParamsAdopted2.stepSizeAdopted2 n) (ParamsAdopted2.numStepsAdopted2 n) y)
      ≤ ∑ y ∈ W, wProf α n y :=
  Finset.sum_le_sum (tail_of_transport''RW2 hn hα hq hA₀ hwin hr hy hprop)

/-- **Transfer 2 — the terminal count.**  `terminal_le_wProfT` summed. -/
theorem sum_terminal_le_wProfT (hn : 3 ≤ n)
    (hq : ∀ j : (Fin n → ℤ), ∀ i ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫)
    (hA₀ : ∀ y ∈ W, (1 : ℝ) < ⟪A₀, q y⟫)
    (hwin : ∀ y ∈ W, ‖toE n y‖ + Real.sqrt n / 2 ≤ windowR2 α n)
    (hr : ∀ y ∈ W, 0 < α * ‖toE n y‖)
    (hy : ∀ k, k < ParamsAdopted2.numStepsAdopted2 n → k ≠ 0 → ∀ y ∈ W,
      0 < yOf (a0C n) ((k : ℝ) * ParamsAdopted2.stepSizeAdopted2 n) (α * ‖toE n y‖))
    (hprop : ∀ k, k < ParamsAdopted2.numStepsAdopted2 n → k ≠ 0 → ∀ y ∈ W,
      P {ω | ∃ i ≤ k, constraintM q W A₀ ξ y i ω ≤ 0}
        ≤ ENNReal.ofReal (4 * Phi (yOf (a0C n)
            ((k : ℝ) * ParamsAdopted2.stepSizeAdopted2 n) (α * ‖toE n y‖)))) :
    ∑ y ∈ W, ENNReal.ofReal (P.real {ω | y ∈ contactSet q W A₀ ξ
        (ParamsAdopted2.numStepsAdopted2 n - 1) ω}) ≤ ∑ y ∈ W, wProfT α n y :=
  Finset.sum_le_sum (terminal_le_wProfT hn hq hA₀ hwin hr hy hprop)

end Transfer

open Classical in
/-- **One §5 selection, both facts, for the chain the drift side runs.**  `sums_split_windowR2`
followed by the two transfers, at `W' := windowOfR2`.  Nothing here mentions `Theorem2R3.wR2`, and
the `LightContact` hypothesis is at the `g`-free profile weights on `shellR`. -/
theorem both_sums_windowR2 {p m : ℕ} [NeZero p] {A B : ℝ} (Q : ChainRaw2RW2 p (m + 1))
    {g : Fin (m + 1) → ZMod p} {θ θ₁ θ₂ : ℝ≥0∞}
    {Ωc : Type*} [MeasurableSpace Ωc] {P : Measure Ωc} [IsProbabilityMeasure P]
    {Ec : Type*} [NormedAddCommGroup Ec] [InnerProductSpace ℝ Ec] [FiniteDimensional ℝ Ec]
    {qm : (Fin (m + 1) → ℤ) → Ec} {A₀ : Ec} {ξ : ℕ → Ωc → Ec} (hn : 3 ≤ m + 1)
    (hsupp : Q.supp = RawDataInst2RW2.shellR Q.alpha (m + 1))
    (hθ0 : θ ≠ 0) (hθt : θ ≠ ⊤)
    (h : Theorem2.LightContact (combW A B (chainRaw3_of_raw2 Q)) Q.supp θ g)
    (h₁ : θ ≤ ENNReal.ofReal A * θ₁) (h₂ : θ ≤ ENNReal.ofReal B * θ₂)
    (hq : ∀ j : (Fin (m + 1) → ℤ),
      ∀ i ∈ DriftStopped8R5.windowOfR2 Q.alpha p m g, (0 : ℝ) ≤ ⟪qm i, qm j⟫)
    (hA₀ : ∀ y ∈ DriftStopped8R5.windowOfR2 Q.alpha p m g, (1 : ℝ) < ⟪A₀, qm y⟫)
    (hwin : ∀ y ∈ DriftStopped8R5.windowOfR2 Q.alpha p m g,
      ‖toE (m + 1) y‖ + Real.sqrt ((m + 1 : ℕ) : ℝ) / 2 ≤ windowR2 Q.alpha (m + 1))
    (hr : ∀ y ∈ DriftStopped8R5.windowOfR2 Q.alpha p m g, 0 < Q.alpha * ‖toE (m + 1) y‖)
    (hy : ∀ k, k < ParamsAdopted2.numStepsAdopted2 (m + 1) → k ≠ 0 →
      ∀ y ∈ DriftStopped8R5.windowOfR2 Q.alpha p m g,
        0 < yOf (a0C (m + 1)) ((k : ℝ) * ParamsAdopted2.stepSizeAdopted2 (m + 1))
          (Q.alpha * ‖toE (m + 1) y‖))
    (hprop : ∀ k, k < ParamsAdopted2.numStepsAdopted2 (m + 1) → k ≠ 0 →
      ∀ y ∈ DriftStopped8R5.windowOfR2 Q.alpha p m g,
        P {ω | ∃ i ≤ k, constraintM qm (DriftStopped8R5.windowOfR2 Q.alpha p m g) A₀ ξ y i ω ≤ 0}
          ≤ ENNReal.ofReal (4 * Phi (yOf (a0C (m + 1))
              ((k : ℝ) * ParamsAdopted2.stepSizeAdopted2 (m + 1))
              (Q.alpha * ‖toE (m + 1) y‖)))) :
    (∑ y ∈ DriftStopped8R5.windowOfR2 Q.alpha p m g,
        ENNReal.ofReal (ContactIntegrated.intWeight P
          (contactSet qm (DriftStopped8R5.windowOfR2 Q.alpha p m g) A₀ ξ)
          (ParamsAdopted2.stepSizeAdopted2 (m + 1))
          (ParamsAdopted2.numStepsAdopted2 (m + 1)) y)) < θ₁ ∧
      (∑ y ∈ DriftStopped8R5.windowOfR2 Q.alpha p m g,
        ENNReal.ofReal (P.real {ω | y ∈ contactSet qm
          (DriftStopped8R5.windowOfR2 Q.alpha p m g) A₀ ξ
          (ParamsAdopted2.numStepsAdopted2 (m + 1) - 1) ω})) < θ₂ := by
  obtain ⟨hs1, hs2⟩ := sums_split_windowR2 (chainRaw3_of_raw2 Q) hsupp hθ0 hθt h h₁ h₂
  exact ⟨lt_of_le_of_lt
      (sum_intWeight_le_wProf (P := P) hn Q.alpha_pos hq hA₀ hwin hr hy hprop) hs1,
    lt_of_le_of_lt
      (sum_terminal_le_wProfT (P := P) hn hq hA₀ hwin hr hy hprop) hs2⟩

end

end Submission.L10.TailAtStepR5W2

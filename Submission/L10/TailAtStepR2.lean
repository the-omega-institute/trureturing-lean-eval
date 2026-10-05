import Submission.L10.TailAtStepR
import Submission.L10.ThetaTight
import Submission.L10.Theorem2R

/-!
# Gate L-10 (`klartag_packing`), brief 81 — `params_of_raw2R` at `windowR` with `thetaTight`

Report 80 fixed the line: `theta := ThetaTight.thetaTight`, not `16·C`.  `Params.markov` is stated
in `ℝ≥0∞` while `ThetaTight.two_mul_lt_thetaTight_mul` is in `ℝ`, so `markov_tight` below is the
lift — the tight analogue of `Lemma43D.markov_of_arith`, and the piece of this brief that needs
nothing from brief 71.

**What brief 71 still owes**, and why it cannot be worked around: `Lemma43Uniform.radial_bound_of_chain`
carries `hWdef : W = radiusOf a₀ α (√n/2) T (Real.log n)` — the **old** endpoint — while
`WindowR.windowR α n = radiusOf (a0C n) α (√n/2) (horizon n) (YR n)`.  So `radial_bound` and the
constant `C` are exactly brief 71's `radial_bound_of_chain'`/`C1R`, and `params_of_raw2R` is stated
here **parameterised on them**: give me the pair and the fold-in is one `exact`.
`Lemma43UniformR.lean` exists and compiles, but carries only the analytic pieces (`pieces_four`,
`hgbound_at'`, `C1cR`, `KcR`); it has no `radial_bound_of_chain'`, `C1R`, `fR` or `params_of_chainR`.
-/

set_option linter.unusedSectionVars false

namespace Submission.L10.TailAtStepR2

open MeasureTheory Set Real Finset
open scoped ENNReal NNReal
open Submission.L10 Submission.L10.Increments Submission.L10.ChainDataInst
open Submission.L10.Tiling Submission.L10.Section5 Submission.L10.ConstructionA
open Submission.L10.WindowR

noncomputable section

/-! ## 1. `markov` at the tight threshold -/

/-- **`Params.markov` at `thetaTight`.**  `Lemma43D.markov_of_arith` proves it for
`theta = ofReal (16·C₁)`; this is the same statement for `theta = ofReal (thetaTight p n C)`, which
report 77 shows is smaller by `α⁻ⁿ/n`.  The content is `ThetaTight.two_mul_lt_thetaTight_mul`
transported across `ENNReal.ofReal`. -/
theorem markov_tight {p n : ℕ} (hn : 0 < n) (hp : 1 < p) {C : ℝ} (hC : 0 < C) :
    2 * (((p - 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal ((n : ℝ) * kappa n * C))
      < ENNReal.ofReal (ThetaTight.thetaTight p n C) * ((p ^ n - 1 : ℕ) : ℝ≥0∞) := by
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hpnN : 1 < p ^ n := Nat.one_lt_pow (by omega) hp
  have hpnR : (1 : ℝ) < (p : ℝ) ^ n := by exact_mod_cast hpnN
  have hκ : 0 < kappa n := kappa_pos hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hd : (0 : ℝ) < (p : ℝ) ^ n - 1 := by linarith
  have hprod : 0 < ((p : ℝ) - 1) * (n : ℝ) * kappa n * C := by positivity
  have hkey := ThetaTight.two_mul_lt_thetaTight_mul (n := n) hpnR hprod
  have hθ0 : 0 ≤ ThetaTight.thetaTight p n C := by
    rw [ThetaTight.thetaTight]
    exact div_nonneg (by positivity) (by linarith)
  have e1 : (((p - 1 : ℕ) : ℝ≥0∞)) = ENNReal.ofReal ((p : ℝ) - 1) := by
    have hr : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub (le_of_lt hp), Nat.cast_one]
    rw [← ENNReal.ofReal_natCast, hr]
  have e2 : (((p ^ n - 1 : ℕ) : ℝ≥0∞)) = ENNReal.ofReal ((p : ℝ) ^ n - 1) := by
    have hr : ((p ^ n - 1 : ℕ) : ℝ) = (p : ℝ) ^ n - 1 := by
      rw [Nat.cast_sub (le_of_lt hpnN), Nat.cast_pow, Nat.cast_one]
    rw [← ENNReal.ofReal_natCast, hr]
  have hL : (2 : ℝ≥0∞) * (ENNReal.ofReal ((p : ℝ) - 1)
        * ENNReal.ofReal ((n : ℝ) * kappa n * C))
      = ENNReal.ofReal (2 * (((p : ℝ) - 1) * ((n : ℝ) * kappa n * C))) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_mul (le_of_lt hp1)]
    norm_num
  have hR : ENNReal.ofReal (ThetaTight.thetaTight p n C) * ENNReal.ofReal ((p : ℝ) ^ n - 1)
      = ENNReal.ofReal (ThetaTight.thetaTight p n C * ((p : ℝ) ^ n - 1)) :=
    (ENNReal.ofReal_mul hθ0).symm
  rw [e1, e2, hL, hR]
  refine (ENNReal.ofReal_lt_ofReal_iff (by linarith [hkey, hprod])).2 ?_
  have hassoc : ((p : ℝ) - 1) * ((n : ℝ) * kappa n * C)
      = ((p : ℝ) - 1) * (n : ℝ) * kappa n * C := by ring
  rw [hassoc]
  exact hkey

/-! ## 2. Lemma 4.3's profile at the reach window -/

/-- `TailAtStep.fC4` at `windowR`: the `4·∫ profile` that `ChainRaw2R.tail` and `dom_of_tail2`
produce.  (Brief 71's `fR` is the same integral without the `4`; when it lands this is `4 * fR`.) -/
def fR4 (α : ℝ) (n : ℕ) : ℝ → ℝ := fun r =>
  4 * ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n), profile (a0C n) α (windowR α n) n t r

theorem fR4_nonneg (α : ℝ) (n : ℕ) (r : ℝ) : 0 ≤ fR4 α n r := by
  have h : (0 : ℝ) ≤ ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
      profile (a0C n) α (windowR α n) n t r :=
    setIntegral_nonneg measurableSet_Ioc (fun t _ => profile_nonneg t r)
  unfold fR4
  linarith

/-! ## 3. `Params` at the reach window, parameterised on brief 71's radial bound -/

/-- **`TailAtStep.params_of_raw2` at `windowR`, with `theta := thetaTight`.**  Every field is
supplied except Lemma 4.3's constant and radial bound at the new endpoint, which are the two
arguments — brief 71's `C1R` and `radial_bound_of_chain'`. -/
def params_of_raw2R_of_radial {p n : ℕ} [Fact (Nat.Prime p)] (hn : 2073600 ≤ n)
    (Q : ChainRaw2R p n) {C : ℝ} (hC : 0 < C)
    (hrad : ∫ y in Ioi (0 : ℝ), y ^ (n - 1) * fR4 Q.alpha n y ≤ C) : Params p n where
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
  windowRadius := windowR Q.alpha n
  window_lt_p := Q.window_lt_p
  f := fR4 Q.alpha n
  f_nonneg := fR4_nonneg Q.alpha n
  w := Q.w
  supp := Q.supp
  supp_ne_zero := Q.supp_ne_zero
  supp_radius := Q.supp_radius
  dom := dom_of_tail2 (by omega) Q.alpha_pos (by norm_num) Q.w Q.supp Q.tail
  integrable := by
    have h := integrable_radial_euclidean (a₀ := a0C n) (α := Q.alpha)
      (W := windowR Q.alpha n) (T := ChainDrift.horizon n) (n := n)
      (T_nonneg (by omega : 1 ≤ n))
    exact h.const_mul 4
  C := C
  radial_bound := hrad
  theta := ENNReal.ofReal (ThetaTight.thetaTight p n C)
  theta_ne_zero := by
    have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Nat.Prime.one_lt (Fact.out : Nat.Prime p))
    have hpn : (1 : ℝ) < (p : ℝ) ^ n :=
      one_lt_pow₀ hpR (by omega)
    have hκ : 0 < kappa n := kappa_pos (by omega)
    have hnR : (0 : ℝ) < (n : ℝ) := by
      have : (0 : ℕ) < n := by omega
      exact_mod_cast this
    have : 0 < ThetaTight.thetaTight p n C := by
      rw [ThetaTight.thetaTight]
      apply div_pos (by positivity) (by linarith)
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    linarith
  theta_ne_top := ENNReal.ofReal_ne_top
  markov :=
    markov_tight (n := n) (p := p) (by omega)
      (Nat.Prime.one_lt (Fact.out : Nat.Prime p)) hC

/-! ## 4. The five `ParamsProducerR` equalities -/

/-- Four of `Theorem2R.ParamsProducerR`'s five equalities are `rfl` on the record above. -/
theorem params_fields {p n : ℕ} [Fact (Nat.Prime p)] (hn : 2073600 ≤ n)
    (Q : ChainRaw2R p n) {C : ℝ} (hC : 0 < C)
    (hrad : ∫ y in Ioi (0 : ℝ), y ^ (n - 1) * fR4 Q.alpha n y ≤ C) :
    (params_of_raw2R_of_radial hn Q hC hrad).alpha = Q.alpha ∧
      (params_of_raw2R_of_radial hn Q hC hrad).R = Q.R ∧
      (params_of_raw2R_of_radial hn Q hC hrad).supp = Q.supp ∧
      (params_of_raw2R_of_radial hn Q hC hrad).w = Q.w ∧
      (params_of_raw2R_of_radial hn Q hC hrad).theta
        = ENNReal.ofReal (ThetaTight.thetaTight p n C) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end

end Submission.L10.TailAtStepR2

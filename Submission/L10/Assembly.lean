import Submission.L10.ChainWiring
import Submission.L10.ChainDataInst
import Submission.L10.LatticeTransfer

/-!
# Gate L-10 (`klartag_packing`) — final assembly, part 1: expectation to existence

Brief 17, goal 1.  The chain's drift bound is a statement about an *expectation*
(`ChainWiring.logdet_bound_chain`); Klartag's Lemma 5.2 (p. 23) turns it into the existence of a
single good `ω`, and eq. (68) turns that into a volume.  Three steps, all deterministic or
elementary:

1. `exists_mem_le_of_integral_lt` — **expectation to existence**, on the good event.  If
   `∫ f < M'·P(S) + m₀·P(Sᶜ)` and `f ≥ m₀` pointwise, some `ω ∈ S` has `f ω ≤ M'`.  The paper's
   "with positive probability" (p. 23) needs the good event too, because `A_T` is only controlled
   there; splitting the integral is what supplies both at once.
2. `drift_to_lemma52` — the arithmetic that turns the drift bound's `κ·N·(d − K)` into Klartag's
   `4 log n`, using `T = 16 log n / n²` and `d = n(n+1)/2 ≥ n²/2`.  **This is where the `n²` is
   produced**, and the inequality is exact: `(T/2)·(n²/2) = 4 log n`.
3. `det_le_of_logDet_le`, `volume_ge_of_logDet_le` — eq. (68): `log det A ≤ C' − 4 log n` gives
   `Vol(E_A) ≥ e^{−C'/2}·n²·Vol(Bⁿ)`, with the constant written out.

Nothing here is probabilistic beyond step 1's integral split; the chain's conditional-law inputs
are briefs 6, 12 and 15's, and enter through `logdet_bound_chain`'s `DriftInputs`.
-/

set_option linter.unusedSectionVars false

namespace Submission.L10.Assembly

open MeasureTheory Matrix Metric Finset
open scoped ENNReal RealInnerProductSpace
open Submission.L10 Submission.L10.Increments

/-! ## 1. Expectation to existence -/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Expectation to existence, on a prescribed event.**  Klartag's "with positive probability
`log det A_T ≤ C' − 4 log n`" (p. 23), strengthened to land inside the good event: if the mean of
`f` is below the value a path outside `S` would already force, some path *in* `S` is below `M'`.

`m₀` is the pointwise lower bound on `f`; for `f = log det A_k` it is `log c_L`, Klartag eq. (32),
supplied by `ChainWiring.det_ge_of_volume_le` and Minkowski's first theorem. -/
theorem exists_mem_le_of_integral_lt [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Integrable f μ)
    {S : Set Ω} (hS : MeasurableSet S) {m₀ M' : ℝ} (hlow : ∀ ω, m₀ ≤ f ω)
    (hlt : ∫ ω, f ω ∂μ < M' * μ.real S + m₀ * μ.real Sᶜ) :
    ∃ ω ∈ S, f ω ≤ M' := by
  by_contra hcon
  have hgt : ∀ ω ∈ S, M' < f ω := by
    intro ω hω
    by_contra hle
    exact hcon ⟨ω, hω, not_lt.1 hle⟩
  have hSfin : μ S < ⊤ := measure_lt_top μ S
  have hScfin : μ Sᶜ < ⊤ := measure_lt_top μ _
  have h1 : M' * μ.real S ≤ ∫ ω in S, f ω ∂μ := by
    have hmono := setIntegral_mono_on ((integrable_const M').integrableOn)
      hf.integrableOn hS (fun ω hω => (hgt ω hω).le)
    rwa [setIntegral_const, smul_eq_mul, mul_comm] at hmono
  have h2 : m₀ * μ.real Sᶜ ≤ ∫ ω in Sᶜ, f ω ∂μ := by
    have hmono := setIntegral_mono_on ((integrable_const m₀).integrableOn)
      hf.integrableOn hS.compl (fun ω _ => hlow ω)
    rwa [setIntegral_const, smul_eq_mul, mul_comm] at hmono
  have h3 : ∫ ω in S, f ω ∂μ + ∫ ω in Sᶜ, f ω ∂μ = ∫ ω, f ω ∂μ :=
    integral_add_compl hS hf
  linarith

/-- The convenient form: on a good event of probability at least `1 − q`, with `M' ≥ m₀`. -/
theorem exists_mem_le_of_integral_le [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Integrable f μ)
    {S : Set Ω} (hS : MeasurableSet S) {m₀ M M' q : ℝ} (hlow : ∀ ω, m₀ ≤ f ω)
    (hq : μ.real Sᶜ ≤ q) (hM : ∫ ω, f ω ∂μ ≤ M) (hm₀ : m₀ ≤ M')
    (hroom : M < M' - q * (M' - m₀)) :
    ∃ ω ∈ S, f ω ≤ M' := by
  refine exists_mem_le_of_integral_lt hf hS hlow (lt_of_le_of_lt hM ?_)
  have hSc : μ.real S = 1 - μ.real Sᶜ := by
    rw [probReal_compl_eq_one_sub hS]; ring
  have hq0 : 0 ≤ μ.real Sᶜ := measureReal_nonneg
  rw [hSc]
  nlinarith [sub_nonneg.2 hm₀]

/-! ## 2. The drift bound's arithmetic — where the `n²` is produced -/

/-- **`(T/2)·(n²/2) = 4 log n` exactly.**  This is the pinned trade-off of report 7 §6.1 in the
form the drift bound consumes. -/
theorem horizon_half_mul {n : ℕ} (hn : n ≠ 0) :
    ChainDrift.horizon n / 2 * ((n : ℝ) ^ 2 / 2) = 4 * Real.log n := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  rw [ChainDrift.horizon]
  field_simp
  ring

/-- **The drift's dimension term dominates `4ρ log n`.**  With `κ·N = T·ρ/2`, `d = n(n+1)/2` and
`K` the expected contact count, the drift `κ·N·(d − K)` is at least `4ρ log n − (Tρ/2)·K`. -/
theorem drift_to_lemma52 {n : ℕ} (hn : n ≠ 0) {ρ K : ℝ} (hρ : 0 ≤ ρ) :
    4 * ρ * Real.log n - (ChainDrift.horizon n * ρ / 2) * K
      ≤ (ChainDrift.horizon n * ρ / 2) * ((n : ℝ) * ((n : ℝ) + 1) / 2 - K) := by
  have hn' : (0 : ℝ) < (n : ℝ) := by
    have : n ≠ 0 := hn
    positivity
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hT : 0 ≤ ChainDrift.horizon n := by
    rw [ChainDrift.horizon]; positivity
  have hkey : (n : ℝ) ^ 2 / 2 ≤ (n : ℝ) * ((n : ℝ) + 1) / 2 := by nlinarith
  have hexact := horizon_half_mul hn
  have hmul : ChainDrift.horizon n * ρ / 2 * ((n : ℝ) ^ 2 / 2)
      = 4 * ρ * Real.log n := by
    have : ChainDrift.horizon n * ρ / 2 * ((n : ℝ) ^ 2 / 2)
        = ρ * (ChainDrift.horizon n / 2 * ((n : ℝ) ^ 2 / 2)) := by ring
    rw [this, hexact]; ring
  have hcoef : 0 ≤ ChainDrift.horizon n * ρ / 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hkey hcoef]

/-! ## 3. Eq. (68): from `log det` to volume -/

variable {N : ℕ}

theorem det_le_of_logDet_le {A : EuclideanSpace ℝ (UT N)} (hApos : 0 < (symMat A).det)
    {M' : ℝ} (hlog : ChainWiring.logDet A ≤ M') : (symMat A).det ≤ Real.exp M' := by
  have h := Real.exp_le_exp.2 hlog
  rwa [ChainWiring.logDet, Real.exp_log hApos] at h

/-- **Klartag eq. (68), with the constant written out.**  `log det A ≤ C' − 4 log n` gives
`Vol(E_A) ≥ e^{−C'/2}·n²·Vol(Bᴺ)`.  With `C'` the universal constant of Lemma 5.2 this is
`c₀ = e^{−C'/2}`: **the `n²` of the theorem statement, produced here and nowhere else.** -/
theorem sqrt_det_le {A : Matrix (Fin N) (Fin N) ℝ} (hApos : 0 < A.det) {C' : ℝ} {n : ℕ}
    (hn : n ≠ 0) (hlog : Real.log A.det ≤ C' - 4 * Real.log n) :
    Real.sqrt A.det ≤ Real.exp (C' / 2) / (n : ℝ) ^ 2 := by
  have hn' : (0 : ℝ) < (n : ℝ) := by positivity
  have hu : 0 < Real.sqrt A.det := Real.sqrt_pos.2 hApos
  have hv : 0 < Real.exp (C' / 2) / (n : ℝ) ^ 2 := by positivity
  refine (Real.log_le_log_iff hu hv).1 ?_
  have hlu : Real.log (Real.sqrt A.det) = Real.log A.det / 2 := Real.log_sqrt hApos.le
  have hlv : Real.log (Real.exp (C' / 2) / (n : ℝ) ^ 2) = C' / 2 - 2 * Real.log n := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_exp, Real.log_pow]
    push_cast
    ring
  rw [hlu, hlv]
  linarith

theorem volume_ge_of_logDet_le {A S : Matrix (Fin N) (Fin N) ℝ} (hApos : 0 < A.det)
    (hS : Sᵀ * A * S = 1) {C' : ℝ} {n : ℕ} (hn : n ≠ 0)
    (hlog : Real.log A.det ≤ C' - 4 * Real.log n) :
    ENNReal.ofReal (Real.exp (-C' / 2) * (n : ℝ) ^ 2
        * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1)).toReal)
      ≤ volume (ChainEllipsoid.ellipsoid A) := by
  have hn' : (0 : ℝ) < (n : ℝ) := by positivity
  have hB0 : (0 : ℝ) ≤ (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1)).toReal :=
    ENNReal.toReal_nonneg
  refine ChainEllipsoid.volume_ellipsoid_ge hApos hS ?_
  have hD0 : (0 : ℝ) ≤ Real.exp (-C' / 2) * (n : ℝ) ^ 2
      * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1)).toReal := by positivity
  have hexp : Real.exp (C' / 2) * Real.exp (-C' / 2) = 1 := by
    rw [← Real.exp_add, show C' / 2 + -C' / 2 = 0 by ring, Real.exp_zero]
  have hnz : ((n : ℝ) ^ 2) ≠ 0 := by positivity
  set B := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1)).toReal with hBdef
  calc Real.sqrt A.det * (Real.exp (-C' / 2) * (n : ℝ) ^ 2 * B)
      ≤ (Real.exp (C' / 2) / (n : ℝ) ^ 2) * (Real.exp (-C' / 2) * (n : ℝ) ^ 2 * B) :=
        mul_le_mul_of_nonneg_right (sqrt_det_le hApos hn hlog) hD0
    _ = (Real.exp (C' / 2) * Real.exp (-C' / 2)) * (((n : ℝ) ^ 2)⁻¹ * (n : ℝ) ^ 2) * B := by
        rw [div_eq_mul_inv]; ring
    _ = B := by rw [hexp, inv_mul_cancel₀ hnz]; ring

/-! ## 4. The chain-side theorem

`exists_phi_of_lemma52` is the lattice-level composition; `exists_phi_of_params` is the
`Params`-level one, which is what brief 13's `ChainDataInst` hands over.  In both, everything
after the chain's own output is proved here. -/

open Submission.L10.ConstructionA Submission.L10.ChainDataInst Submission.L10.LatticeTransfer
open Submission.L10.Section5 Submission.L10.Tiling

/-- **What the probabilistic half must still deliver, at the lattice level.**  Klartag's
Lemma 5.2 (p. 23) together with "`A_T` is almost surely `L`-free" (p. 24). -/
def Lemma52 (m : ℕ) (c₀ : ℝ) : Prop :=
  ∃ (L : Submodule ℤ (Fin (m + 1) → ℝ)) (_ : DiscreteTopology L) (_ : IsZLattice ℝ L)
    (A S : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ),
    0 < A.det ∧ Sᵀ * A * S = 1 ∧
    (∀ x : Fin (m + 1) → ℝ, x ∈ L → x ≠ 0 →
      (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (m + 1))) ∉ ChainEllipsoid.ellipsoid A) ∧
    ZLattice.covolume L * Real.sqrt A.det * (c₀ * (m : ℝ) ^ 2)
      ≤ (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)).toReal

/-- **The chain side, end to end.**  Lemma 5.2 gives the challenge's `φ` for that dimension. -/
theorem exists_phi_of_lemma52 {m : ℕ} {c₀ : ℝ} (h : Lemma52 m c₀) :
    ∃ φ : EuclideanSpace ℝ (Fin (m + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (m + 1)),
      ENNReal.ofReal (c₀ * (m : ℝ) ^ 2) ≤ volume (φ '' Metric.ball 0 1) ∧
      {v ∈ φ '' Metric.ball 0 1 | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} := by
  obtain ⟨L, hdt, hzl, A, S, hApos, hS, hfree, hdet⟩ := h
  have := hdt
  have := hzl
  obtain ⟨A', S', hA'pos, hS', hvol, hint⟩ := chain_hyp_of_lattice L hApos hS hfree hdet
  refine ⟨Matrix.toEuclideanLin S', ?_, ?_⟩
  · rw [ChainEllipsoid.image_ball_eq_ellipsoid hS']
    exact ChainEllipsoid.volume_ellipsoid_ge hA'pos hS' hvol
  · rw [ChainEllipsoid.image_ball_eq_ellipsoid hS']
    exact hint

/-- **What the chain must deliver for one set of parameters**, in Klartag's eq. (68)
normalisation `√(det A)·c₀·m² ≤ 1` (report 13's `transfer_det_of_eq68`). -/
def ChainOutput {p m : ℕ} (α : ℝ) (g : Fin (m + 1) → ZMod p) (c₀ : ℝ) : Prop :=
  ∃ A S : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ, 0 < A.det ∧ Sᵀ * A * S = 1 ∧
    Real.sqrt A.det * (c₀ * (m : ℝ) ^ 2) ≤ 1 ∧
    ∀ x : Fin (m + 1) → ℝ, x ∈ (α • ·) '' (latR p (m + 1) g : Set (Fin (m + 1) → ℝ)) → x ≠ 0 →
      (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (m + 1))) ∉ ChainEllipsoid.ellipsoid A

theorem mulVec_ne_zero {N : ℕ} {B : Matrix (Fin N) (Fin N) ℝ} (hB : B.det ≠ 0)
    {v : Fin N → ℝ} (hv : v ≠ 0) : B *ᵥ v ≠ 0 := by
  intro h
  refine hv ?_
  have hinv : B⁻¹ *ᵥ (B *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul B (isUnit_iff_ne_zero.2 hB),
      Matrix.one_mulVec]
  rw [h, Matrix.mulVec_zero] at hinv
  exact hinv.symm

/-- **Goal 2.**  From the chain's parameters and its output to the challenge's `φ`, for the
dimension `m + 1`. -/
theorem exists_phi_of_params {p m : ℕ} [Fact (Nat.Prime p)] [NeZero p] (P : Params p (m + 1))
    {c₀ : ℝ}
    (hchain : ∀ g : Fin (m + 1) → ZMod p, g ≠ 0 →
      (∀ y : Fin (m + 1) → ℤ, y ≠ 0 → ‖toE (m + 1) y‖ ≤ P.R → y ∉ latZ p (m + 1) g) →
      ChainOutput P.alpha g c₀) :
    ∃ φ : EuclideanSpace ℝ (Fin (m + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (m + 1)),
      ENNReal.ofReal (c₀ * (m : ℝ) ^ 2) ≤ volume (φ '' Metric.ball 0 1) ∧
      {v ∈ φ '' Metric.ball 0 1 | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} := by
  obtain ⟨g, hg0, hfreeR, _⟩ := exists_good_line_of_params P
  obtain ⟨A, S, hApos, hS, heq68, hfree⟩ := hchain g hg0 hfreeR
  obtain ⟨B, hBdet, hBabs, hBmem⟩ :=
    exists_scaled_basisMatrix (p := p) (n := m + 1) (Nat.le_add_left 1 m) P.alpha_pos
      P.alpha_norm hg0
  have hfreeB : ∀ y : Fin (m + 1) → ℤ, y ≠ 0 →
      (WithLp.toLp 2 (B *ᵥ (fun i => (y i : ℝ))) : EuclideanSpace ℝ (Fin (m + 1)))
        ∉ ChainEllipsoid.ellipsoid A := by
    intro y hy
    refine hfree _ (hBmem y) (mulVec_ne_zero hBdet ?_)
    intro hz
    refine hy (funext fun i => ?_)
    have hzi := congrFun hz i
    simp only [Pi.zero_apply] at hzi ⊢
    exact_mod_cast hzi
  obtain ⟨A', S', hA'pos, hS', hvol, hint⟩ :=
    chain_hyp_of_transfer hApos hS hBdet hfreeB (transfer_det_of_eq68 hBabs heq68)
  refine ⟨Matrix.toEuclideanLin S', ?_, ?_⟩
  · rw [ChainEllipsoid.image_ball_eq_ellipsoid hS']
    exact ChainEllipsoid.volume_ellipsoid_ge hA'pos hS' hvol
  · rw [ChainEllipsoid.image_ball_eq_ellipsoid hS']
    exact hint

end Submission.L10.Assembly

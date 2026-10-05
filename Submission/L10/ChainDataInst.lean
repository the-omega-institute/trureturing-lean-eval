import Mathlib
import Submission.L10.Section5
import Submission.L10.Lemma43
import Submission.L10.ChainDrift
import Submission.L10.LatticeTransfer

/-!
# Gate L-10 (`klartag_packing`) — H9, and `ChainData` from the chain's parameters

Brief 13, goals 2 and 3.

## H9 — the expected accumulated contact count

Report 7 §4.5 settles a modelling question the discretisation raises and the paper does not:
contact points need not persist, so `C_N` is the **accumulated** set and Proposition 4.2 must be
read for it.  `expected_card_le` is that reading, and it is pure linearity of expectation: the
per-point tail (Prop 4.1, brief 2's `padded_increment_tail`) and §5's contact bound are its two
hypotheses, and `E|C_N| ≤ 2θ + E` its conclusion — report 7's `4K + C·exp(-cn)` at `θ = 2K`.

## `ChainData` from the parameters

`Params p n` names every number the chain fixes — the scale `α`, Klartag's `a₀`, the Use-1 radius
`R`, the horizon `T` and discretisation `N`, `h` of report 7 §6.3, the window radius, and Lemma
4.3's radial data — and `chainData_of_params` turns it into `Section5.ChainData p n`.  The
composite `exists_good_line_of_params` then delivers §5's line `g` directly from the parameters.

`a0_gt_one_iff` is the one place `a₀` is *used*: Klartag's `a₀·|x|² > 1` (p. 21, eq. 61) is
exactly `|x| > 1 - 1/n`, which is §5's radius condition on the scaled lattice.

## Meeting H10

`exists_scaled_basisMatrix` produces the matrix `B = α·B₀` that
`LatticeTransfer.chain_hyp_of_transfer` consumes, with `|det B| = κ_n` already — so
`transfer_det_of_eq68` reduces that theorem's determinant hypothesis to Klartag's eq. (68) in its
paper form, `√(det A)·(c·m²) ≤ 1`.
-/

open MeasureTheory Metric Set Finset Matrix
open scoped ENNReal

namespace Submission.L10.ChainDataInst

open Submission.L10.ConstructionA Submission.L10.Tiling Submission.L10.Section5
open Submission.L10.LatticeTransfer Submission.L10.ChainEllipsoid

variable {p n : ℕ}

/-! ### H9 — the expected accumulated contact count -/

/-- **H9.**  Proposition 4.2 read for the *accumulated* contact set (report 7 §4.5).  Linearity
of expectation over the window turns a per-point tail bound (Prop 4.1, brief 2's
`padded_increment_tail`) plus §5's contact bound into `E|C_N| ≤ 2θ + E`.

With `θ` the Markov threshold of `Section5.ChainData` and `E = C·e^{-cn}` the Corollary 3.2
excursion term, this is report 7's `H9 : ∫ ω, |C_m| ≤ 4K + C·exp(-cn)` at `θ = 2K`. -/
theorem expected_card_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {ι : Type*} [DecidableEq ι] (W : Finset ι) (Cset : Ω → Finset ι)
    (hsub : ∀ ω, Cset ω ⊆ W)
    (hmeas : ∀ i ∈ W, MeasurableSet {ω | i ∈ Cset ω})
    (weight err : ι → ℝ)
    (htail : ∀ i ∈ W, μ.real {ω | i ∈ Cset ω} ≤ 2 * weight i + err i)
    {θ E : ℝ} (hθ : ∑ i ∈ W, weight i ≤ θ) (hE : ∑ i ∈ W, err i ≤ E) :
    ∫ ω, ((Cset ω).card : ℝ) ∂μ ≤ 2 * θ + E := by
  classical
  have hcard : ∀ ω, ((Cset ω).card : ℝ)
      = ∑ i ∈ W, Set.indicator {ω | i ∈ Cset ω} (fun _ => (1 : ℝ)) ω := by
    intro ω
    have hfil : W.filter (fun i => i ∈ Cset ω) = Cset ω := by
      ext i
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨hsub ω h, h⟩⟩
    rw [← hfil, Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases hi : i ∈ Cset ω <;> simp [Set.indicator, hi]
  have hint : ∀ i ∈ W, Integrable
      (fun ω => Set.indicator {ω | i ∈ Cset ω} (fun _ => (1 : ℝ)) ω) μ :=
    fun i hi => (integrable_const (1 : ℝ)).indicator (hmeas i hi)
  calc ∫ ω, ((Cset ω).card : ℝ) ∂μ
      = ∫ ω, ∑ i ∈ W, Set.indicator {ω | i ∈ Cset ω} (fun _ => (1 : ℝ)) ω ∂μ := by
        simp_rw [hcard]
    _ = ∑ i ∈ W, ∫ ω, Set.indicator {ω | i ∈ Cset ω} (fun _ => (1 : ℝ)) ω ∂μ :=
        integral_finsetSum W hint
    _ = ∑ i ∈ W, μ.real {ω | i ∈ Cset ω} :=
        Finset.sum_congr rfl (fun i hi => integral_indicator_one (hmeas i hi))
    _ ≤ ∑ i ∈ W, (2 * weight i + err i) := Finset.sum_le_sum htail
    _ = 2 * (∑ i ∈ W, weight i) + ∑ i ∈ W, err i := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 2 * θ + E := by
        have h2 : 2 * (∑ i ∈ W, weight i) ≤ 2 * θ := by linarith
        linarith

/-! ### Klartag's `a₀` and §5's radius -/

/-- Klartag's `a₀·|x|² > 1` (p. 21, eq. 61) is exactly `|x| > 1 - 1/n`, which is §5's radius
condition on the *scaled* lattice. -/
theorem a0_gt_one_iff {a0 r : ℝ} {n : ℕ} (ha0 : a0 = (1 - 1 / (n : ℝ))⁻¹ ^ 2)
    (hpos : 0 < 1 - 1 / (n : ℝ)) (hr : 0 ≤ r) :
    1 < a0 * r ^ 2 ↔ 1 - 1 / (n : ℝ) < r := by
  subst ha0
  rw [inv_pow, ← div_eq_inv_mul, lt_div_iff₀ (by positivity)]
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

/-! ### The chain's parameters -/

/-- **The chain's parameters, as §5 consumes them.**

`alpha`, `R` and `tiling_defect` are §5's arithmetic; `a0`, `T`, `N` and `h` pin the chain's
constants so that the two halves cannot drift apart (§5 uses `a0` only through
`a0_gt_one_iff`, and does not use `T`, `N`, `h` at all — they shape `w`, `f` and `C`);
`windowRadius` through `markov` is Lemma 4.3's data, in the shape
`Submission.L10.weight_bound_of_radial` (report 9) consumes.

The two `_lt_p` fields are the only place `p`'s size is used: they discharge both
indivisibility fields through `Section5.redMod_ne_zero_of_norm_lt`. -/
structure Params (p n : ℕ) where
  dim_pos : 1 ≤ n
  /-- The lattice scale: `αⁿ·p^{n-1} = κ_n`, so `covol(α·Λ(g)) = Vol(Bⁿ)`. -/
  alpha : ℝ
  alpha_pos : 0 < alpha
  alpha_norm : alpha ^ n * ((p ^ (n - 1) : ℕ) : ℝ) = kappa n
  /-- Klartag's `a₀ = (1-1/n)⁻²`, p. 21 eq. (61). -/
  a0 : ℝ
  a0_eq : a0 = (1 - 1 / (n : ℝ))⁻¹ ^ 2
  /-- The unscaled Use-1 radius; `α·R ≤ 1 - 1/n` is `a₀·|αx|² > 1` by `a0_gt_one_iff`. -/
  R : ℝ
  R_nonneg : 0 ≤ R
  R_scaled : alpha * R ≤ 1 - 1 / (n : ℝ)
  R_lt_p : R < (p : ℝ)
  tiling_defect : (n : ℝ) * (alpha * Real.sqrt n / 2) ≤ 1 / 4
  /-- The horizon `T = 16 log n / n²` and the discretisation adopted in report 7 §6.3:
  `N = ⌈16 n⁵ log n⌉`, `h = T/N`.  Pinned here so §§2–4 and §5 agree; §5 does not read them. -/
  T : ℝ
  T_eq : T = ChainDrift.horizon n
  N : ℕ
  N_eq : N = ChainDrift.numSteps n 5
  h : ℝ
  h_eq : h = ChainDrift.stepSize n 5
  /-- The window: eq. (55)'s shell `R_t`, unscaled. -/
  windowRadius : ℝ
  window_lt_p : windowRadius < (p : ℝ)
  /-- Lemma 4.3's radial profile, already widened to the cube's worst point. -/
  f : ℝ → ℝ
  f_nonneg : ∀ r : ℝ, 0 ≤ f r
  /-- Eq. (65)'s contact weight and its finite support. -/
  w : (Fin n → ℤ) → ℝ≥0∞
  supp : Finset (Fin n → ℤ)
  supp_ne_zero : ∀ y ∈ supp, y ≠ 0
  supp_radius : ∀ y ∈ supp, ‖toE n y‖ ≤ windowRadius
  dom : ∀ y ∈ supp, ∀ x ∈ cube (toE n y), w y ≤ ENNReal.ofReal (f ‖x‖)
  integrable : Integrable (fun x : EuclideanSpace ℝ (Fin n) => f ‖x‖)
  /-- Lemma 4.3's number: `C = C₁·e^{n²T/8}/n` in the paper's notation. -/
  C : ℝ
  radial_bound : ∫ y in Set.Ioi (0 : ℝ), y ^ (n - 1) * f y ≤ C
  /-- Markov's threshold, `16C₁n⁻²e^{n²T/8}`. -/
  theta : ℝ≥0∞
  theta_ne_zero : theta ≠ 0
  theta_ne_top : theta ≠ ⊤
  markov : 2 * (((p - 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal ((n : ℝ) * kappa n * C))
      < theta * ((p ^ n - 1 : ℕ) : ℝ≥0∞)

/-- **`ChainData` from the chain's parameters.** -/
def chainData_of_params [Fact (Nat.Prime p)] [NeZero p] (P : Params p n) : ChainData p n where
  dim_pos := P.dim_pos
  alpha := P.alpha
  alpha_pos := P.alpha_pos
  alpha_norm := P.alpha_norm
  R := P.R
  R_nonneg := P.R_nonneg
  R_scaled := P.R_scaled
  tiling_defect := P.tiling_defect
  w := P.w
  supp := P.supp
  theta := P.theta
  theta_ne_zero := P.theta_ne_zero
  theta_ne_top := P.theta_ne_top
  weight_bound :=
    Submission.L10.weight_bound_of_radial P.dim_pos P.supp P.w P.f P.f_nonneg P.dom
      P.integrable P.radial_bound P.theta P.markov
  ball_indivisible := fun _y hy0 hyR =>
    redMod_ne_zero_of_norm_lt hy0 (lt_of_le_of_lt hyR P.R_lt_p)
  supp_indivisible := fun y hy =>
    redMod_ne_zero_of_norm_lt (P.supp_ne_zero y hy)
      (lt_of_le_of_lt (P.supp_radius y hy) P.window_lt_p)

/-- **The composite.**  From the chain's parameters to §5's single line `g`. -/
theorem exists_good_line_of_params [Fact (Nat.Prime p)] [NeZero p] (P : Params p n) :
    ∃ g : Fin n → ZMod p, g ≠ 0 ∧
      (∀ y : Fin n → ℤ, y ≠ 0 → ‖toE n y‖ ≤ P.R → y ∉ latZ p n g) ∧
      ∑ y ∈ P.supp.filter (fun y => y ∈ latZ p n g), P.w y < P.theta :=
  exists_good_line_of_chainData (chainData_of_params P)

/-! ### The scaled basis matrix: §5's line meets H10 -/

/-- **The scaled basis matrix.**  `B = α·B₀`, where `B₀(ℤⁿ) = Λ(g)`, satisfies
`B(ℤⁿ) = α·Λ(g)` and — by report 3's `covolume_latR` together with the normalisation
`αⁿ·p^{n-1} = κ_n` — `|det B| = κ_n`.  This is the matrix `LatticeTransfer.chain_hyp_of_transfer`
consumes, and it makes that theorem's determinant hypothesis Klartag's eq. (68) verbatim:
`κ_n·√(det A)·c·m² ≤ κ_n`, i.e. `√(det A)·c·m² ≤ 1`. -/
theorem exists_scaled_basisMatrix [Fact (Nat.Prime p)] [NeZero p] (hn : 1 ≤ n)
    {α : ℝ} (hα : 0 < α) (hnorm : α ^ n * ((p ^ (n - 1) : ℕ) : ℝ) = kappa n)
    {g : Fin n → ZMod p} (hg : g ≠ 0) :
    ∃ B : Matrix (Fin n) (Fin n) ℝ, B.det ≠ 0 ∧ |B.det| = kappa n ∧
      ∀ y : Fin n → ℤ, B *ᵥ (fun i => (y i : ℝ)) ∈ (α • ·) '' (latR p n g : Set (Fin n → ℝ)) := by
  obtain ⟨B₀, hB₀det, hB₀cov, hB₀mem⟩ := exists_basisMatrix (latR p n g)
  refine ⟨α • B₀, ?_, ?_, ?_⟩
  · rw [Matrix.det_smul]
    exact mul_ne_zero (by positivity) hB₀det
  · rw [Matrix.det_smul, abs_mul, abs_pow, abs_of_pos hα, Fintype.card_fin, hB₀cov,
      covolume_latR hn g hg, ← hnorm]
    push_cast
    ring
  · intro y
    refine ⟨B₀ *ᵥ (fun i => (y i : ℝ)), (hB₀mem _).2 ⟨y, rfl⟩, ?_⟩
    rw [Matrix.smul_mulVec]

/-- **The determinant condition, in Klartag's eq. (68) form.**  With `|det B| = κ_n` the
transfer's hypothesis reduces to `√(det A)·(c·m²) ≤ 1`: the chain's `det A_T ≤ C/n⁴` with
`c ≤ C^{-1/2}`. -/
theorem transfer_det_of_eq68 {m : ℕ} {A B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ} {c : ℝ}
    (hB : |B.det| = kappa (m + 1))
    (heq68 : Real.sqrt A.det * (c * (m : ℝ) ^ 2) ≤ 1) :
    Real.sqrt (B.det ^ 2 * A.det) * (c * (m : ℝ) ^ 2)
      ≤ (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)).toReal := by
  have hsq : Real.sqrt (B.det ^ 2 * A.det) = |B.det| * Real.sqrt A.det := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs]
  have hk : kappa (m + 1) = (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)).toReal :=
    rfl
  have hkpos : 0 ≤ kappa (m + 1) := kappa_nonneg _
  rw [hsq, hB, ← hk, mul_assoc]
  calc kappa (m + 1) * (Real.sqrt A.det * (c * (m : ℝ) ^ 2))
      ≤ kappa (m + 1) * 1 := by exact mul_le_mul_of_nonneg_left heq68 hkpos
    _ = kappa (m + 1) := mul_one _

end Submission.L10.ChainDataInst

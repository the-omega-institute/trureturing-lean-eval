import Mathlib

/-!
# Gate L-10, hinge 3 — the operator-norm tail of a random symmetric matrix

This file supports brief 1 of gate L-10 (`klartag_packing`). It contains

* **Part 1** (proved): an explicit `ε`-net of the unit sphere of a finite-dimensional real
  normed space with at most `(1 + 2/ε) ^ d` points, obtained from a maximal `ε`-separated
  finite set and a Haar-measure packing count.
* **Part 2** (proved): for a self-adjoint continuous linear map `T` on a real inner product
  space, `(1 - 2ε) * ‖T‖ ≤ M` whenever `|⟪T x, x⟫| ≤ M` on an `ε`-net of the unit sphere.
  The ingredient `GateL10.opNorm_le_of_quadratic` (`‖T‖ ≤ M` from `|⟪T x, x⟫| ≤ M` on the
  unit sphere, for self-adjoint `T`) is proved here by polarization. Mathlib also has it, as
  `ContinuousLinearMap.norm_eq_iSup_rayleighQuotient` (`Analysis/InnerProductSpace/Rayleigh.lean`)
  together with `ContinuousLinearMap.opNorm_le_of_re_inner_le`
  (`Analysis/InnerProductSpace/LinearMap.lean`); routing through those would shorten this file.
* **Part 3** (proved): the coefficient bound for the quadratic form, `∑ (i,j), (2 x i x j)^2
  ≤ 4`, which is the sub-Gaussian variance proxy of `⟪A x, x⟫` for a unit vector `x`;
  and `union_bound_arith`, the numeric step of the union bound.
* **Part 4** (statement only): `GateL10.OpNormTail`, the Lean statement of Klartag,
  arXiv:2504.05042, Corollary 3.2 (p. 13), in the form the discrete chain of hinge 1 needs.

Reference: B. Klartag, *Lattice packing of spheres in high dimensions using a stochastically
evolving ellipsoid*, arXiv:2504.05042 v2, Corollary 3.2, p. 13; Vershynin, *High-Dimensional
Probability*, Corollary 4.4.8 and Lemma 4.4.1.
-/

namespace GateL10

open Metric MeasureTheory Module Set Finset
open scoped ENNReal NNReal RealInnerProductSpace

/-! ## Part 1. An explicit `ε`-net of the unit sphere -/

section Net

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E]

/-- `IsSeparated ε N` : `N` is a finite set of unit vectors, any two distinct ones at
distance more than `ε`. Note that Mathlib has an unrelated `Metric.IsSeparated`; this one is
`GateL10.IsSeparated` and shadows it inside this namespace only. -/
def IsSeparated (ε : ℝ) (N : Finset E) : Prop :=
  (∀ x ∈ N, ‖x‖ = 1) ∧ ∀ x ∈ N, ∀ y ∈ N, x ≠ y → ε < dist x y

/-- **Packing count.** An `ε`-separated set of unit vectors has at most `(1 + 2/ε) ^ d`
elements, `d = finrank ℝ E`. The proof is the volume argument: the balls of radius `ε/2`
around the points are pairwise disjoint and contained in the ball of radius `1 + ε/2`. -/
theorem card_le_of_isSeparated (μ : Measure E) [μ.IsAddHaarMeasure]
    {ε : ℝ} (hε : 0 < ε) {N : Finset E} (h : IsSeparated ε N) :
    (N.card : ℝ) ≤ (1 + 2 / ε) ^ finrank ℝ E := by
  classical
  have hε2 : (0 : ℝ) ≤ ε / 2 := by linarith
  have hε2' : (0 : ℝ) ≤ 1 + ε / 2 := by linarith
  have hVpos : 0 < μ.real (ball (0 : E) 1) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (measure_ball_pos μ 0 one_pos).ne' measure_ball_lt_top.ne
  have hball : ∀ (x : E) (r : ℝ), 0 ≤ r →
      μ.real (ball x r) = r ^ finrank ℝ E * μ.real (ball (0 : E) 1) := by
    intro x r hr
    rw [measureReal_def, Measure.addHaar_ball μ x hr, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg hr _), measureReal_def]
  -- the small balls are pairwise disjoint
  have hdisj : (↑N : Set E).PairwiseDisjoint (fun x : E => ball x (ε / 2)) := by
    intro x hx y hy hxy
    simp only [Function.onFun]
    rw [Set.disjoint_left]
    intro z hz hz'
    have h1 : dist z x < ε / 2 := mem_ball.mp hz
    have h2 : dist z y < ε / 2 := mem_ball.mp hz'
    have hlt : dist x y < ε := by
      calc dist x y ≤ dist x z + dist z y := dist_triangle _ _ _
        _ < ε / 2 + ε / 2 := by rw [dist_comm x z]; exact add_lt_add h1 h2
        _ = ε := by ring
    exact absurd hlt
      (not_lt.mpr (h.2 x (Finset.mem_coe.mp hx) y (Finset.mem_coe.mp hy) hxy).le)
  -- they all sit inside the ball of radius `1 + ε/2`
  have hsub : (⋃ x ∈ N, ball x (ε / 2)) ⊆ ball (0 : E) (1 + ε / 2) := by
    intro z hz
    simp only [Set.mem_iUnion, exists_prop] at hz
    obtain ⟨x, hxN, hzx⟩ := hz
    have hx1 : dist x 0 = 1 := by rw [dist_zero_right]; exact h.1 x hxN
    rw [mem_ball]
    calc dist z 0 ≤ dist z x + dist x 0 := dist_triangle _ _ _
      _ < ε / 2 + 1 := by rw [hx1]; linarith [mem_ball.mp hzx]
      _ = 1 + ε / 2 := by ring
  have h1 : ∑ x ∈ N, μ.real (ball x (ε / 2)) ≤ μ.real (ball (0 : E) (1 + ε / 2)) := by
    rw [← measureReal_biUnion_finset hdisj (fun b _ => measurableSet_ball)]
    exact measureReal_mono hsub measure_ball_lt_top.ne
  have hsum : ∑ x ∈ N, μ.real (ball x (ε / 2))
      = ∑ _x ∈ N, ((ε / 2) ^ finrank ℝ E * μ.real (ball (0 : E) 1)) :=
    Finset.sum_congr rfl fun x _ => hball x (ε / 2) hε2
  rw [hsum, hball 0 (1 + ε / 2) hε2', Finset.sum_const, nsmul_eq_mul, ← mul_assoc] at h1
  have h2 : (N.card : ℝ) * (ε / 2) ^ finrank ℝ E ≤ (1 + ε / 2) ^ finrank ℝ E :=
    le_of_mul_le_mul_right h1 hVpos
  have hpos : (0 : ℝ) < (ε / 2) ^ finrank ℝ E := pow_pos (by linarith) _
  have h3 : (N.card : ℝ) ≤ (1 + ε / 2) ^ finrank ℝ E / (ε / 2) ^ finrank ℝ E :=
    (le_div_iff₀ hpos).mpr h2
  have h4 : (1 + ε / 2) / (ε / 2) = 1 + 2 / ε := by
    field_simp
    ring
  rwa [← div_pow, h4] at h3

/-- **Existence of an `ε`-net of the unit sphere with an explicit cardinality bound.**
A maximal `ε`-separated set of unit vectors is an `ε`-net, and the packing count bounds its
size. Existence of a maximal one is `Nat.sSup_mem`: the set of achievable cardinalities is a
nonempty set of naturals bounded above by the packing count. -/
theorem exists_net (μ : Measure E) [μ.IsAddHaarMeasure] {ε : ℝ} (hε : 0 < ε) :
    ∃ N : Finset E, (∀ x ∈ N, ‖x‖ = 1) ∧ (N.card : ℝ) ≤ (1 + 2 / ε) ^ finrank ℝ E ∧
      ∀ z : E, ‖z‖ = 1 → ∃ y ∈ N, ‖z - y‖ ≤ ε := by
  classical
  set C : Set ℕ := {k | ∃ N : Finset E, IsSeparated ε N ∧ N.card = k} with hC
  have hCne : C.Nonempty := ⟨0, ∅, ⟨by simp, by simp⟩, rfl⟩
  have hCbdd : BddAbove C := by
    refine ⟨⌈(1 + 2 / ε) ^ finrank ℝ E⌉₊, ?_⟩
    rintro k ⟨N, hN, rfl⟩
    exact Nat.cast_le.mp ((card_le_of_isSeparated μ hε hN).trans (Nat.le_ceil _))
  obtain ⟨N, hNsep, hNcard⟩ := Nat.sSup_mem hCne hCbdd
  refine ⟨N, hNsep.1, card_le_of_isSeparated μ hε hNsep, ?_⟩
  intro z hz
  by_contra hcon
  push Not at hcon
  have hzN : z ∉ N := by
    intro hmem
    have hcc := hcon z hmem
    simp only [sub_self, norm_zero] at hcc
    linarith
  have hins : IsSeparated ε (insert z N) := by
    constructor
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hz
      · exact hNsep.1 x hx
    · intro a ha b hb hab
      have key : ∀ w ∈ N, ε < dist z w := by
        intro w hw
        rw [dist_eq_norm]
        exact hcon w hw
      rcases Finset.mem_insert.mp ha with ha' | ha' <;>
        rcases Finset.mem_insert.mp hb with hb' | hb'
      · exact absurd (ha'.trans hb'.symm) hab
      · rw [ha']; exact key b hb'
      · rw [hb', dist_comm]; exact key a ha'
      · exact hNsep.2 a ha' b hb' hab
  have hcard : (insert z N).card = sSup C + 1 := by
    rw [Finset.card_insert_of_notMem hzN, hNcard]
  have hle : sSup C + 1 ≤ sSup C := le_csSup hCbdd ⟨insert z N, hins, hcard⟩
  omega

end Net

/-! ## Part 2. The operator norm from the net -/

section OpNorm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- For a self-adjoint continuous linear map on a real inner product space, the operator norm
is bounded by any bound on the quadratic form over the unit sphere. This is the classical
polarization argument, proved here self-containedly. Mathlib carries the same fact in the form
`ContinuousLinearMap.norm_eq_iSup_rayleighQuotient` (`‖T‖ = ⨆ x, |T.rayleighQuotient x|` for a
symmetric `T`), built on `ContinuousLinearMap.opNorm_le_of_re_inner_le`; deriving this statement
from those is the shorter route. -/
theorem opNorm_le_of_quadratic (T : E →L[ℝ] E) (hT : ∀ x y : E, ⟪T x, y⟫ = ⟪x, T y⟫)
    {M : ℝ} (hM : 0 ≤ M) (h : ∀ x : E, ‖x‖ = 1 → |⟪T x, x⟫| ≤ M) : ‖T‖ ≤ M := by
  have hscale : ∀ (r : ℝ) (v : E), ⟪T (r • v), r • v⟫ = r ^ 2 * ⟪T v, v⟫ := by
    intro r v
    simp only [map_smul, real_inner_smul_left, real_inner_smul_right]
    ring
  -- the quadratic form bound, homogenised
  have hq : ∀ x : E, |⟪T x, x⟫| ≤ M * ‖x‖ ^ 2 := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    have hu1 : ‖(‖x‖⁻¹ • x : E)‖ = 1 := by
      rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x),
        inv_mul_cancel₀ hxn]
    have hx2 : ⟪T x, x⟫ = ‖x‖ ^ 2 * ⟪T (‖x‖⁻¹ • x), (‖x‖⁻¹ • x : E)⟫ := by
      rw [← hscale ‖x‖ (‖x‖⁻¹ • x), smul_smul, mul_inv_cancel₀ hxn, one_smul]
    rw [hx2, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖x‖ ^ 2)]
    calc ‖x‖ ^ 2 * |⟪T (‖x‖⁻¹ • x), (‖x‖⁻¹ • x : E)⟫| ≤ ‖x‖ ^ 2 * M :=
          mul_le_mul_of_nonneg_left (h _ hu1) (by positivity)
      _ = M * ‖x‖ ^ 2 := by ring
  -- polarization identity
  have expand : ∀ u v : E, ⟪T (u + v), u + v⟫ - ⟪T (u - v), u - v⟫
      = 2 * ⟪T u, v⟫ + 2 * ⟪T v, u⟫ := by
    intro u v
    simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
    ring
  -- `‖T x‖ ≤ M` on the unit sphere
  have hunit : ∀ x : E, ‖x‖ = 1 → ‖T x‖ ≤ M := by
    intro x hx
    rcases eq_or_ne (T x) 0 with hTx | hTx
    · rw [hTx, norm_zero]; exact hM
    have hTxn : ‖T x‖ ≠ 0 := norm_ne_zero_iff.mpr hTx
    set y : E := ‖T x‖⁻¹ • T x with hy
    have hy1 : ‖y‖ = 1 := by
      rw [hy, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
        inv_mul_cancel₀ hTxn]
    have hxy : ⟪T x, y⟫ = ‖T x‖ := by
      rw [hy, real_inner_smul_right, real_inner_self_eq_norm_sq, sq, ← mul_assoc,
        inv_mul_cancel₀ hTxn, one_mul]
    have hsym : ⟪T y, x⟫ = ⟪T x, y⟫ := (real_inner_comm x (T y)).trans (hT x y).symm
    have h4 : 4 * ‖T x‖ = ⟪T (x + y), x + y⟫ - ⟪T (x - y), x - y⟫ := by
      rw [expand x y, hsym, hxy]; ring
    have hpar : ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 4 := by
      rw [parallelogram_law_with_norm ℝ x y, hx, hy1]; norm_num
    have hb1 : ⟪T (x + y), x + y⟫ ≤ M * ‖x + y‖ ^ 2 := (abs_le.mp (hq (x + y))).2
    have hb2 : -(M * ‖x - y‖ ^ 2) ≤ ⟪T (x - y), x - y⟫ := (abs_le.mp (hq (x - y))).1
    have hMsum : M * ‖x + y‖ ^ 2 + M * ‖x - y‖ ^ 2 = 4 * M := by
      rw [← mul_add, hpar]; ring
    linarith
  -- conclude by homogeneity
  refine T.opNorm_le_bound hM fun x => ?_
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hu1 : ‖(‖x‖⁻¹ • x : E)‖ = 1 := by
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x),
      inv_mul_cancel₀ hxn]
  have hxu : x = ‖x‖ • (‖x‖⁻¹ • x : E) := by
    rw [smul_smul, mul_inv_cancel₀ hxn, one_smul]
  calc ‖T x‖ = ‖x‖ * ‖T (‖x‖⁻¹ • x : E)‖ := by
        conv_lhs => rw [hxu]
        rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)]
    _ ≤ ‖x‖ * M := mul_le_mul_of_nonneg_left (hunit _ hu1) (norm_nonneg x)
    _ = M * ‖x‖ := by ring

/-- **The net bound** (Vershynin, *High-Dimensional Probability*, Lemma 4.4.1, symmetric
case). If the quadratic form of a self-adjoint `T` is bounded by `M` on an `ε`-net of the unit
sphere, then `(1 - 2ε) * ‖T‖ ≤ M`. -/
theorem opNorm_le_of_net {ε : ℝ} (hε0 : 0 < ε) (N : Finset E)
    (hNsph : ∀ x ∈ N, ‖x‖ = 1) (hN : ∀ z : E, ‖z‖ = 1 → ∃ y ∈ N, ‖z - y‖ ≤ ε)
    (T : E →L[ℝ] E) (hT : ∀ x y : E, ⟪T x, y⟫ = ⟪x, T y⟫)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ x ∈ N, |⟪T x, x⟫| ≤ M) :
    (1 - 2 * ε) * ‖T‖ ≤ M := by
  have hεT : 0 ≤ 2 * ε * ‖T‖ := mul_nonneg (by linarith) (norm_nonneg T)
  have hM' : 0 ≤ M + 2 * ε * ‖T‖ := by linarith
  have step : ∀ x : E, ‖x‖ = 1 → |⟪T x, x⟫| ≤ M + 2 * ε * ‖T‖ := by
    intro x hx
    obtain ⟨y, hyN, hxy⟩ := hN x hx
    have hy1 : ‖y‖ = 1 := hNsph y hyN
    have e1 : ⟪T x, x⟫ - ⟪T y, y⟫ = ⟪T x, x - y⟫ + ⟪T (x - y), y⟫ := by
      simp only [map_sub, inner_sub_left, inner_sub_right]
      ring
    have hTx : ‖T x‖ ≤ ‖T‖ := by
      have := T.le_opNorm x
      rwa [hx, mul_one] at this
    have b1 : |⟪T x, x - y⟫| ≤ ‖T‖ * ε :=
      (abs_real_inner_le_norm _ _).trans
        (mul_le_mul hTx hxy (norm_nonneg _) (norm_nonneg _))
    have b2 : |⟪T (x - y), y⟫| ≤ ‖T‖ * ε := by
      refine (abs_real_inner_le_norm _ _).trans ?_
      have hh : ‖T (x - y)‖ ≤ ‖T‖ * ε :=
        (T.le_opNorm (x - y)).trans (mul_le_mul_of_nonneg_left hxy (norm_nonneg T))
      calc ‖T (x - y)‖ * ‖y‖ = ‖T (x - y)‖ := by rw [hy1, mul_one]
        _ ≤ ‖T‖ * ε := hh
    have b3 : |⟪T y, y⟫| ≤ M := hbound y hyN
    have habs : |⟪T x, x⟫| ≤ |⟪T y, y⟫| + (|⟪T x, x - y⟫| + |⟪T (x - y), y⟫|) := by
      have e2 : ⟪T x, x⟫ = ⟪T y, y⟫ + (⟪T x, x - y⟫ + ⟪T (x - y), y⟫) := by linarith
      rw [e2]
      have p1 := abs_add_le (⟪T y, y⟫) (⟪T x, x - y⟫ + ⟪T (x - y), y⟫)
      have p2 := abs_add_le (⟪T x, x - y⟫) (⟪T (x - y), y⟫)
      linarith
    linarith
  have := opNorm_le_of_quadratic T hT hM' step
  linarith

/-- **Steps (1) and (2) combined**, specialised to `EuclideanSpace ℝ (Fin n)` at `ε = 1/4`:
an explicit net of at most `9 ^ n` unit vectors on which the quadratic form controls the
operator norm up to a factor `2`. This is exactly what the union bound of step (4) consumes. -/
theorem exists_net_euclidean (n : ℕ) (hn : 0 < n) :
    ∃ N : Finset (EuclideanSpace ℝ (Fin n)),
      (∀ x ∈ N, ‖x‖ = 1) ∧ (N.card : ℝ) ≤ 9 ^ n ∧
      ∀ T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
        (∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫) → ∀ M : ℝ, 0 ≤ M →
          (∀ x ∈ N, |⟪T x, x⟫| ≤ M) → ‖T‖ ≤ 2 * M := by
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; exact hn)
  obtain ⟨N, h1, h2, h3⟩ :=
    exists_net (E := EuclideanSpace ℝ (Fin n)) volume (ε := 1 / 4) (by norm_num)
  rw [finrank_euclideanSpace_fin] at h2
  refine ⟨N, h1, ?_, ?_⟩
  · have : (1 + 2 / (1 / 4 : ℝ)) = 9 := by norm_num
    rwa [this] at h2
  · intro T hT M hM hb
    have hnet := opNorm_le_of_net (E := EuclideanSpace ℝ (Fin n))
      (by norm_num : (0 : ℝ) < 1 / 4) N h1 h3 T hT hM hb
    linarith

end OpNorm

/-! ## Part 3. Arithmetic inputs to steps (3) and (5) -/

/-- For a unit vector `x`, the coefficients `2 x i x j` of the quadratic form `⟪A x, x⟫` in the
independent entries `A i j` have squares summing to at most `4`. This is the variance-proxy
computation of step (3) of the outline; the sum is over **all** pairs, which dominates the sum
over `i ≤ j`, so the same bound serves after restriction. -/
theorem sum_sq_coeff_le {n : ℕ} (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) :
    ∑ p : Fin n × Fin n, (2 * x p.1 * x p.2) ^ 2 ≤ 4 := by
  have h : ∑ p : Fin n × Fin n, (2 * x p.1 * x p.2) ^ 2
      = 4 * ((∑ i, x i ^ 2) * ∑ j, x j ^ 2) := by
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h, hx]
  norm_num

/-- The numeric step of the union bound (step (5) of the outline): with an `ε = 1/4` net of at
most `9 ^ n` unit vectors and the Chernoff exponent `-(9/2) s² n` obtained at
`u = 6 √c · s · √n`, the union bound is dominated by `exp (-s² n)` for every `s ≥ 1`.
Only `Real.log 9 ≤ 3` is needed, so the constant has ample slack. -/
theorem union_bound_arith {n : ℕ} {s : ℝ} (hs : 1 ≤ s) :
    (9 : ℝ) ^ n * Real.exp (-(9 / 2 * s ^ 2 * n)) ≤ Real.exp (-(s ^ 2 * n)) := by
  have hexp3 : (9 : ℝ) ≤ Real.exp 3 := by
    have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have h0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    have h3 : Real.exp 3 = Real.exp 1 * (Real.exp 1 * Real.exp 1) := by
      rw [← Real.exp_add, ← Real.exp_add]; norm_num
    rw [h3]; nlinarith
  have he : (9 : ℝ) ≤ Real.exp (7 / 2 * s ^ 2) := by
    refine hexp3.trans (Real.exp_le_exp.mpr ?_)
    nlinarith
  have hpow : (9 : ℝ) ^ n ≤ Real.exp (7 / 2 * s ^ 2) ^ n :=
    pow_le_pow_left₀ (by norm_num) he n
  refine (mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le).trans_eq ?_
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  ring

/-- Monotonicity of the sub-Gaussian parameter. Mathlib has `HasSubgaussianMGF.const_mul`,
`.neg`, `.add_of_indepFun` and `.sum_of_iIndepFun`, but no monotonicity lemma at pin
`6f1ef4e5`; step (3) of the outline needs one to replace `∑ p, c p` by a uniform bound. -/
theorem hasSubgaussianMGF_mono {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    {c d : ℝ≥0} (h : ProbabilityTheory.HasSubgaussianMGF X c P) (hcd : c ≤ d) :
    ProbabilityTheory.HasSubgaussianMGF X d P where
  integrable_exp_mul := h.integrable_exp_mul
  mgf_le t := (h.mgf_le t).trans (Real.exp_le_exp.mpr (by
    have hc : (c : ℝ) ≤ (d : ℝ) := by exact_mod_cast hcd
    nlinarith [sq_nonneg t]))

/-! ## Part 4. The statement of Corollary 3.2 -/

/-- **Klartag, arXiv:2504.05042, Corollary 3.2 (p. 13)**, in the form the discrete chain of
hinge 1 needs: a symmetric random matrix whose entries on and above the diagonal are
independent and sub-Gaussian with parameter `c` satisfies, for every `s ≥ 1`,
`P(‖A‖_op ≥ C √c · s · √n) ≤ 4 exp (-s² n)`.

The GOE of the paper is the case `c = 2/n` (`E Γ_ij ^ 2 = (1 + δ_ij)/n`, and a centred Gaussian
of variance `v` is sub-Gaussian with parameter `v`), for which the bound reads
`P(‖Γ‖_op ≥ C √2 · s) ≤ 4 exp (-s² n)`, i.e. Klartag's `P(‖Γ‖_op ≥ C₀ s) ≤ 4 exp (-s² n)`.
The outline of the accompanying report establishes it with `C = 12`.
Hinge 2 §3 records that the value of the constant is not load-bearing downstream. -/
def OpNormTail (C : ℝ) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (A : Ω → Matrix (Fin n) (Fin n) ℝ) (c : ℝ≥0),
    (∀ ω, (A ω).IsSymm) →
    (∀ i j : Fin n, Measurable fun ω => A ω i j) →
    ProbabilityTheory.iIndepFun
      (fun (p : {p : Fin n × Fin n // p.1 ≤ p.2}) (ω : Ω) => A ω p.1.1 p.1.2) P →
    (∀ i j : Fin n, i ≤ j → ProbabilityTheory.HasSubgaussianMGF (fun ω => A ω i j) c P) →
    ∀ s : ℝ, 1 ≤ s →
      P.real {ω | C * Real.sqrt c * s * Real.sqrt n ≤
        ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (A ω)‖} ≤ 4 * Real.exp (-(s ^ 2 * n))

/-- The cheaper equivalent form, and the one the outline recommends proving: the random matrix
is `B + Bᵀ` with the entries of `B` independent, indexed by the **full** product
`Fin n × Fin n`. For Gaussians this is exactly Klartag's GOE — `B i j` i.i.d. `N(0, 1/(2n))`
gives `E (B + Bᵀ) i j ^ 2 = (1 + δ_ij)/n` — and it removes the `i ≤ j` re-indexing from
step (3), because `⟪(B + Bᵀ) x, x⟫ = ∑ p : Fin n × Fin n, (2 * x p.1 * x p.2) * B p.1 p.2`
is already a sum of independent terms over the full product type, with coefficients bounded
by `GateL10.sum_sq_coeff_le`. -/
def OpNormTailSymmetrized (C : ℝ) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (B : Ω → Matrix (Fin n) (Fin n) ℝ) (c : ℝ≥0),
    (∀ i j : Fin n, Measurable fun ω => B ω i j) →
    ProbabilityTheory.iIndepFun (fun (p : Fin n × Fin n) (ω : Ω) => B ω p.1 p.2) P →
    (∀ i j : Fin n, ProbabilityTheory.HasSubgaussianMGF (fun ω => B ω i j) c P) →
    ∀ s : ℝ, 1 ≤ s →
      P.real {ω | C * Real.sqrt c * s * Real.sqrt n ≤
        ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (B ω + (B ω).transpose)‖} ≤ 4 * Real.exp (-(s ^ 2 * n))

end GateL10

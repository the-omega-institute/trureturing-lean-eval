import Mathlib
import Submission.L10.ConstructionA
import Submission.L10.Tiling

/-!
# Gate L-10 (`klartag_packing`) — §5 complete: the two uses, the union bound, and the interface

Brief 5.  With `Submission.L10.ConstructionA` (the finite first moment) and
`Submission.L10.Tiling` (cube packing) in hand, this module closes Klartag's §5
(arXiv:2504.05042, p. 22, eqs. 63–66) and states the exact interface that §§2–4 must meet.

## The design, in one paragraph

Klartag normalises the lattice into `X_n` by scaling it by `α` with `αⁿ·p^{n-1} = κ_n`.  We scale
the **test sets** instead (report 3 §10), so no `covolume (r • L)` lemma is needed — Mathlib has
none.  Use 1 then asks for no nonzero point of `Λ(g) ⊆ ℤⁿ` in the ball of *unscaled* radius
`R = (1-1/n)/α`, and cube packing bounds that count by `volume (ball 0 (R + √n/2))`.  Dividing by
`p^{n-1}` turns that into `(1 - 1/n + δ)ⁿ` with `δ = α√n/2` — hinge 2's bound, with the
cube-tiling defect appearing exactly where hinge 2 predicted.

## Two ways this is cheaper than the paper

* **`e^{-3/4} < 1/2`, not `1/e`.**  `1 - 1/n + δ ≤ exp(-1/n + δ)` gives
  `(1-1/n+δ)ⁿ ≤ exp(-1 + nδ) ≤ exp(-3/4) < 1/2` as soon as `nδ ≤ 1/4`.  The union bound is then
  `1/2 + 1/2 < 1` with strictness coming from Use 1, instead of the paper's `1/e + 1/2`.  Hinge
  2's `δ ≤ n⁻³` is far stronger than needed.
* **No `n₀`.**  `exists_prime_tiling_defect` shows the arithmetic fields of `ChainData` are
  satisfiable for *every* `n ≥ 2`, because `α = (κ_n/p^{n-1})^{1/n} → 0` as `p → ∞`.  The paper's
  "n sufficiently large" belongs to §§3–4, never to §5.

## Main results

* `two_lt_exp_three_quarters`, `two_mul_pow_lt_one` — the Use-1 arithmetic.
* `two_mul_card_lt`, `use_one_arith`, `two_mul_card_bad_one_lt` — **Use 1** (eqs. 63–64).
* `sum_weight_onLine`, `card_bad_two_weighted_le`, `two_mul_card_bad_two_lt` — **Use 2**
  (eqs. 65–66), with *weights*, which is what `K̃_t` actually is.
* `weight_bound_of_lintegral` — the connector from Lemma 4.3's integral to the Markov step.
* `exists_good_line` — **Proposition 5.1**, combined.
* `ChainData` / `exists_good_line_of_chainData` — **the interface**: every fact §5 consumes from
  §§2–4, as named fields, and the single line `g` it returns.
-/

open MeasureTheory Metric Set Finset
open scoped ENNReal

namespace Submission.L10.Section5

open Submission.L10.ConstructionA Submission.L10.Tiling

variable {p n : ℕ}

/-! ### The volume of a Euclidean ball, and the two elementary inequalities -/

/-- `κ_n = Vol_n(Bⁿ)`, as a real number. -/
noncomputable def kappa (n : ℕ) : ℝ :=
  (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal

theorem kappa_pos (hn : 0 < n) : 0 < kappa n := by
  have hne : Nonempty (Fin n) := Fin.pos_iff_nonempty.1 hn
  have h1 : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ 0 :=
    (measure_ball_pos volume 0 one_pos).ne'
  have h2 : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ ⊤ := measure_ball_lt_top.ne
  exact ENNReal.toReal_pos h1 h2

theorem volume_ball_eq (hn : 0 < n) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ρ)
      = ENNReal.ofReal (ρ ^ n * kappa n) := by
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; exact hn)
  rw [Measure.addHaar_ball _ _ hρ, finrank_euclideanSpace_fin, kappa,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hρ,
    ENNReal.ofReal_toReal measure_ball_lt_top.ne]

/-- `2 < exp (3/4)`, via `exp (3/4) = exp (1/8) ^ 6 ≥ (9/8) ^ 6 = 531441/262144`. -/
theorem two_lt_exp_three_quarters : (2 : ℝ) < Real.exp (3 / 4) := by
  have h1 : (9 / 8 : ℝ) ≤ Real.exp (1 / 8) := by
    have := Real.add_one_le_exp (1 / 8 : ℝ)
    linarith
  have h2 : ((9 : ℝ) / 8) ^ 6 ≤ (Real.exp (1 / 8)) ^ 6 :=
    pow_le_pow_left₀ (by norm_num) h1 6
  have h3 : (Real.exp (1 / 8)) ^ 6 = Real.exp (3 / 4) := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h3] at h2
  calc (2 : ℝ) < ((9 : ℝ) / 8) ^ 6 := by norm_num
    _ ≤ Real.exp (3 / 4) := h2

/-- The Use-1 arithmetic core: `x ≤ 1 - 1/n + δ` with `n·δ ≤ 1/4` forces `2·xⁿ < 1`.
This replaces Klartag's `(1-1/n)ⁿ ≤ 1/e` and is *stronger*: `e^{-3/4} < 1/2`, so the
union bound gets `1/2 + 1/2` rather than `1/e + 1/2`, with strictness to spare. -/
theorem two_mul_pow_lt_one (hn : 0 < n) {x δ : ℝ} (hx : 0 ≤ x) (_hδ : 0 ≤ δ)
    (hxle : x ≤ 1 - 1 / (n : ℝ) + δ) (hnδ : (n : ℝ) * δ ≤ 1 / 4) :
    2 * x ^ n < 1 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hstep : x ≤ Real.exp (-(1 / (n : ℝ)) + δ) := by
    have := Real.add_one_le_exp (-(1 / (n : ℝ)) + δ)
    linarith
  have hpow : x ^ n ≤ (Real.exp (-(1 / (n : ℝ)) + δ)) ^ n := pow_le_pow_left₀ hx hstep n
  have hexp : (Real.exp (-(1 / (n : ℝ)) + δ)) ^ n = Real.exp (-1 + (n : ℝ) * δ) := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  have hle : Real.exp (-1 + (n : ℝ) * δ) ≤ Real.exp (-(3 / 4)) := by
    apply Real.exp_le_exp.2
    linarith
  have hhalf : Real.exp (-(3 / 4)) < 1 / 2 := by
    have h := two_lt_exp_three_quarters
    rw [Real.exp_neg]
    rw [inv_lt_iff_one_lt_mul₀ (Real.exp_pos _)]
    linarith
  rw [hexp] at hpow
  linarith [hpow.trans hle]

theorem kappa_nonneg (n : ℕ) : 0 ≤ kappa n := ENNReal.toReal_nonneg

/-! ### Use 1 (eqs. 63–64): the small ball -/

/-- The integer-point count of a ball, in the form the union bound consumes. -/
theorem two_mul_card_lt (hn : 0 < n) {R : ℝ} (hR : 0 ≤ R) {m : ℕ} (A : Finset (Fin n → ℤ))
    (hA : ∀ y ∈ A, ‖toE n y‖ ≤ R)
    (hlt : 2 * ((R + Real.sqrt n / 2) ^ n * kappa n) < (m : ℝ)) :
    2 * A.card < m := by
  have hρ : (0 : ℝ) ≤ R + Real.sqrt n / 2 := by positivity
  have hnn : (0 : ℝ) ≤ (R + Real.sqrt n / 2) ^ n * kappa n :=
    mul_nonneg (pow_nonneg hρ n) (kappa_nonneg n)
  have h1 : (A.card : ℝ≥0∞) ≤ ENNReal.ofReal ((R + Real.sqrt n / 2) ^ n * kappa n) := by
    rw [← volume_ball_eq hn hρ]
    exact card_le_volume_ball hn R A hA
  have h2 : ((A.card : ℕ) : ℝ) ≤ (R + Real.sqrt n / 2) ^ n * kappa n := by
    rw [← ENNReal.ofReal_le_ofReal_iff hnn, ENNReal.ofReal_natCast]
    exact h1
  have h3 : ((2 * A.card : ℕ) : ℝ) < (m : ℝ) := by push_cast; linarith
  exact_mod_cast h3

/-- **The Use-1 volume condition, discharged.**  Under Klartag's normalisation
`αⁿ·m = κ_n` (so that `α·Λ(g)` has covolume `κ_n`), a scaled radius `α·(R + √n/2) ≤ 1 - 1/n + δ`
with `n·δ ≤ 1/4` gives the hypothesis of `two_mul_card_lt`. -/
theorem use_one_arith (hn : 0 < n) {α δ R : ℝ} {m : ℕ} (hα : 0 < α) (hm : 0 < m)
    (hnorm : α ^ n * (m : ℝ) = kappa n) (hR : 0 ≤ R) (hδ : 0 ≤ δ)
    (hRle : α * (R + Real.sqrt n / 2) ≤ 1 - 1 / (n : ℝ) + δ)
    (hnδ : (n : ℝ) * δ ≤ 1 / 4) :
    2 * ((R + Real.sqrt n / 2) ^ n * kappa n) < (m : ℝ) := by
  have hρ : (0 : ℝ) ≤ R + Real.sqrt n / 2 := by positivity
  have key : 2 * (α * (R + Real.sqrt n / 2)) ^ n < 1 :=
    two_mul_pow_lt_one hn (by positivity) hδ hRle hnδ
  have hexp : (R + Real.sqrt n / 2) ^ n * kappa n
      = (α * (R + Real.sqrt n / 2)) ^ n * (m : ℝ) := by
    rw [← hnorm, mul_pow]; ring
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  rw [hexp, ← mul_assoc]
  calc 2 * (α * (R + Real.sqrt n / 2)) ^ n * (m : ℝ)
      < 1 * (m : ℝ) := by exact mul_lt_mul_of_pos_right key hmpos
    _ = (m : ℝ) := one_mul _

/-- **Use 1 (eq. 64), discrete counterpart.**  Fewer than half of the `pⁿ-1` lines meet the
small ball at all. -/
theorem two_mul_card_bad_one_lt [Fact (Nat.Prime p)] (hn : 1 ≤ n) (A : Finset (Fin n → ℤ))
    (hA : ∀ y ∈ A, redMod p y ≠ 0) (hA2 : 2 * A.card < p ^ (n - 1)) :
    2 * ((Finset.univ.erase (0 : Fin n → ZMod p)).filter
        (fun g => ∃ y ∈ A, OnLine g (redMod p y))).card < p ^ n - 1 := by
  classical
  have hp := Fact.out (p := Nat.Prime p)
  have hmpos : 0 < p ^ (n - 1) := pow_pos hp.pos _
  have hMpos : 0 < p ^ n - 1 := by
    have h1 : 1 < p ^ n := by
      calc 1 < p := hp.one_lt
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ n := Nat.pow_le_pow_right hp.pos hn
    omega
  have hbad := card_bad_one_le (p := p) hn A hA
  set b := ((Finset.univ.erase (0 : Fin n → ZMod p)).filter
      (fun g => ∃ y ∈ A, OnLine g (redMod p y))).card with hbdef
  refine Nat.lt_of_mul_lt_mul_left (a := p ^ (n - 1)) ?_
  calc p ^ (n - 1) * (2 * b) = 2 * (p ^ (n - 1) * b) := by ring
    _ ≤ 2 * ((p ^ n - 1) * A.card) := Nat.mul_le_mul_left _ hbad
    _ = (p ^ n - 1) * (2 * A.card) := by ring
    _ < (p ^ n - 1) * p ^ (n - 1) := by
        exact mul_lt_mul_of_pos_left hA2 hMpos
    _ = p ^ (n - 1) * (p ^ n - 1) := by ring

/-! ### Use 2 (eqs. 65–66): the weighted contact count -/

/-- **Weighted first-moment lemma.**  The same swap of two finite sums as
`ConstructionA.sum_card_filter_onLine`, with weights — this is what eq. (65)'s `K̃_t`
(a sum of `Φ`-values, not a bare count) actually needs. -/
theorem sum_weight_onLine [Fact (Nat.Prime p)] (A : Finset (Fin n → ℤ))
    (hA : ∀ y ∈ A, redMod p y ≠ 0) (w : (Fin n → ℤ) → ℝ≥0∞) :
    ∑ g : Fin n → ZMod p, ∑ y ∈ A.filter (fun y => OnLine g (redMod p y)), w y
      = ((p - 1 : ℕ) : ℝ≥0∞) * ∑ y ∈ A, w y := by
  classical
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun y hy => ?_)
  rw [← Finset.sum_filter, Finset.sum_const, card_filter_onLine _ (hA y hy), nsmul_eq_mul]

theorem sum_weight_onLine_erase [Fact (Nat.Prime p)] (A : Finset (Fin n → ℤ))
    (hA : ∀ y ∈ A, redMod p y ≠ 0) (w : (Fin n → ℤ) → ℝ≥0∞) :
    ∑ g ∈ Finset.univ.erase (0 : Fin n → ZMod p),
        ∑ y ∈ A.filter (fun y => OnLine g (redMod p y)), w y
      = ((p - 1 : ℕ) : ℝ≥0∞) * ∑ y ∈ A, w y := by
  classical
  rw [← sum_weight_onLine A hA w, eq_comm,
    ← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : Fin n → ZMod p))]
  have hzero : (A.filter (fun y => OnLine (0 : Fin n → ZMod p) (redMod p y))) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro y hy hcon
    exact hA y hy ((onLine_zero_iff _).1 hcon)
  rw [hzero, Finset.sum_empty, add_zero]

/-- **Weighted Markov (eq. 66).** -/
theorem card_bad_two_weighted_le [Fact (Nat.Prime p)] (B : Finset (Fin n → ℤ))
    (hB : ∀ y ∈ B, redMod p y ≠ 0) (w : (Fin n → ℤ) → ℝ≥0∞) (θ : ℝ≥0∞) :
    θ * (((Finset.univ.erase (0 : Fin n → ZMod p)).filter
        (fun g => θ ≤ ∑ y ∈ B.filter (fun y => OnLine g (redMod p y)), w y)).card : ℝ≥0∞)
      ≤ ((p - 1 : ℕ) : ℝ≥0∞) * ∑ y ∈ B, w y := by
  classical
  rw [← sum_weight_onLine_erase B hB w]
  calc θ * (((Finset.univ.erase (0 : Fin n → ZMod p)).filter
          (fun g => θ ≤ ∑ y ∈ B.filter (fun y => OnLine g (redMod p y)), w y)).card : ℝ≥0∞)
      = ∑ _g ∈ (Finset.univ.erase (0 : Fin n → ZMod p)).filter
          (fun g => θ ≤ ∑ y ∈ B.filter (fun y => OnLine g (redMod p y)), w y), θ := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ g ∈ (Finset.univ.erase (0 : Fin n → ZMod p)).filter
          (fun g => θ ≤ ∑ y ∈ B.filter (fun y => OnLine g (redMod p y)), w y),
          ∑ y ∈ B.filter (fun y => OnLine g (redMod p y)), w y :=
        Finset.sum_le_sum (fun g hg => (Finset.mem_filter.1 hg).2)
    _ ≤ ∑ g ∈ Finset.univ.erase (0 : Fin n → ZMod p),
          ∑ y ∈ B.filter (fun y => OnLine g (redMod p y)), w y :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- **Use 2 (eq. 66), discrete counterpart.**  Fewer than half of the lines carry a weighted
contact sum of `θ` or more. -/
theorem two_mul_card_bad_two_lt [Fact (Nat.Prime p)] (B : Finset (Fin n → ℤ))
    (hB : ∀ y ∈ B, redMod p y ≠ 0) (w : (Fin n → ℤ) → ℝ≥0∞) (θ : ℝ≥0∞)
    (_hθ0 : θ ≠ 0) (_hθtop : θ ≠ ⊤)
    (hB2 : 2 * (((p - 1 : ℕ) : ℝ≥0∞) * ∑ y ∈ B, w y) < θ * ((p ^ n - 1 : ℕ) : ℝ≥0∞)) :
    2 * ((Finset.univ.erase (0 : Fin n → ZMod p)).filter
        (fun g => θ ≤ ∑ y ∈ B.filter (fun y => OnLine g (redMod p y)), w y)).card
      < p ^ n - 1 := by
  classical
  set b := ((Finset.univ.erase (0 : Fin n → ZMod p)).filter
      (fun g => θ ≤ ∑ y ∈ B.filter (fun y => OnLine g (redMod p y)), w y)).card with hbdef
  have hmark := card_bad_two_weighted_le (p := p) B hB w θ
  have hkey : θ * ((2 * b : ℕ) : ℝ≥0∞) < θ * ((p ^ n - 1 : ℕ) : ℝ≥0∞) := by
    calc θ * ((2 * b : ℕ) : ℝ≥0∞) = 2 * (θ * (b : ℝ≥0∞)) := by push_cast; ring
      _ ≤ 2 * (((p - 1 : ℕ) : ℝ≥0∞) * ∑ y ∈ B, w y) := by gcongr
      _ < θ * ((p ^ n - 1 : ℕ) : ℝ≥0∞) := hB2
  have hlt : ((2 * b : ℕ) : ℝ≥0∞) < ((p ^ n - 1 : ℕ) : ℝ≥0∞) := by
    by_contra hcon
    push Not at hcon
    exact absurd hkey (not_lt.2 (by gcongr))
  exact_mod_cast hlt

/-- **From an integral bound to `ChainData.weight_bound`.**  This is the connector between
Lemma 4.3 (`∫ Φ ≤ C₁κ_n e^{n²t/8}`, evaluated by polar coordinates — the Mathlib entry point is
`MeasureTheory.Measure.integral_fun_norm_addHaar`, `Constructions/HaarToSphere.lean:296`) and the
finite Markov step.  The domination hypothesis `hdom` is where radial monotonicity of `Φ` is
used: on the cube at `y`, `Φ` at `y` is below `Φ` at the *inner* radius. -/
theorem weight_bound_of_lintegral [Fact (Nat.Prime p)] (B : Finset (Fin n → ℤ))
    (w : (Fin n → ℤ) → ℝ≥0∞) (ψ : EuclideanSpace ℝ (Fin n) → ℝ≥0∞)
    (hdom : ∀ y ∈ B, ∀ x ∈ Tiling.cube (Tiling.toE n y), w y ≤ ψ x)
    (θ I : ℝ≥0∞) (hI : ∫⁻ x, ψ x ≤ I)
    (hnum : 2 * (((p - 1 : ℕ) : ℝ≥0∞) * I) < θ * ((p ^ n - 1 : ℕ) : ℝ≥0∞)) :
    2 * (((p - 1 : ℕ) : ℝ≥0∞) * ∑ y ∈ B, w y) < θ * ((p ^ n - 1 : ℕ) : ℝ≥0∞) := by
  refine lt_of_le_of_lt ?_ hnum
  gcongr
  exact le_trans (Tiling.sum_le_lintegral B w ψ hdom) hI

/-! ### Proposition 5.1, combined -/

/-- **Proposition 5.1 (Construction A form), weighted.**  `1/2 + 1/2 < 1`: Use 1 kills fewer
than half the lines, Use 2 kills fewer than half, so a line survives both. -/
theorem exists_good_line [Fact (Nat.Prime p)] (hn : 1 ≤ n)
    (A B : Finset (Fin n → ℤ)) (hA : ∀ y ∈ A, redMod p y ≠ 0) (hB : ∀ y ∈ B, redMod p y ≠ 0)
    (w : (Fin n → ℤ) → ℝ≥0∞) (θ : ℝ≥0∞) (hθ0 : θ ≠ 0) (hθtop : θ ≠ ⊤)
    (hAsize : 2 * A.card < p ^ (n - 1))
    (hBsize : 2 * (((p - 1 : ℕ) : ℝ≥0∞) * ∑ y ∈ B, w y) < θ * ((p ^ n - 1 : ℕ) : ℝ≥0∞)) :
    ∃ g : Fin n → ZMod p, g ≠ 0 ∧ (∀ y ∈ A, ¬ OnLine g (redMod p y)) ∧
      ∑ y ∈ B.filter (fun y => OnLine g (redMod p y)), w y < θ := by
  classical
  set s : Finset (Fin n → ZMod p) := Finset.univ.erase 0 with hs
  set B₁ := s.filter (fun g => ∃ y ∈ A, OnLine g (redMod p y)) with hB₁
  set B₂ := s.filter (fun g => θ ≤ ∑ y ∈ B.filter (fun y => OnLine g (redMod p y)), w y) with hB₂
  have h1 : 2 * B₁.card < p ^ n - 1 := two_mul_card_bad_one_lt hn A hA hAsize
  have h2 : 2 * B₂.card < p ^ n - 1 := two_mul_card_bad_two_lt B hB w θ hθ0 hθtop hBsize
  have hcard : s.card = p ^ n - 1 := card_erase_univ
  have hlt : B₁.card + B₂.card < s.card := by rw [hcard]; omega
  obtain ⟨g, hgs, hg1, hg2⟩ := exists_mem_not_mem hlt
  refine ⟨g, (Finset.mem_erase.1 hgs).1, ?_, ?_⟩
  · intro y hy hcon
    exact hg1 (Finset.mem_filter.2 ⟨hgs, ⟨y, hy, hcon⟩⟩)
  · by_contra hcon
    exact hg2 (Finset.mem_filter.2 ⟨hgs, not_lt.1 hcon⟩)

/-! ### The interface with the chain (§§2–4) -/

/-- Membership in Construction A is decidable, so the contact sum below is a plain `Finset.sum`. -/
instance decidableMemLatZ [NeZero p] (g : Fin n → ZMod p) :
    DecidablePred (fun y : Fin n → ℤ => y ∈ latZ p n g) :=
  fun y => decidable_of_iff _ (mem_latZ_iff_onLine g y).symm

/-- **The §5 ⇄ chain interface.**

Every fact §5 consumes from the rest of the proof, as named fields.  §§2–4 (brief 2's chain,
brief 1's tail) supply the *analytic* data — the radius `R`, the contact weight `w` on its finite
support, and the integral bound behind `weight_bound`.  §5 supplies the *arithmetic* and returns
one line `g`.  Nothing else passes between the halves.

The scale `α` is Klartag's normalisation: `αⁿ · p^{n-1} = κ_n` makes `covol (α·Λ(g)) = Vol(Bⁿ)`,
i.e. `α·Λ(g) ∈ X_n` (p. 21).  Following report 3 §10 the scaling is applied to the *test sets*,
never to the lattice, so no `covolume (r • L)` lemma is needed: `R` is the unscaled radius
`(1-1/n)/α`, and `w` is evaluated at `α·y`. -/
structure ChainData (p n : ℕ) where
  /-- `n ≥ 1`.  The challenge's `n = 0` is `Scaling.case_zero`. -/
  dim_pos : 1 ≤ n
  /-- The lattice scale. -/
  alpha : ℝ
  alpha_pos : 0 < alpha
  /-- `αⁿ · p^{n-1} = κ_n`: the scaled lattice sits in Klartag's `X_n` on the nose. -/
  alpha_norm : alpha ^ n * ((p ^ (n - 1) : ℕ) : ℝ) = kappa n
  /-- Use 1's unscaled radius; `α·R ≤ 1 - 1/n` is Klartag's `a₀ = (1-1/n)⁻²` condition. -/
  R : ℝ
  R_nonneg : 0 ≤ R
  R_scaled : alpha * R ≤ 1 - 1 / (n : ℝ)
  /-- The cube-tiling defect `δ = α√n/2`.  `n·δ ≤ 1/4` is all §5 needs; hinge 2's `δ ≤ n⁻³` is
  far stronger than necessary, and the defect costs the union bound nothing. -/
  tiling_defect : (n : ℝ) * (alpha * Real.sqrt n / 2) ≤ 1 / 4
  /-- Use 2's contact weight and its finite support (eq. 65's `K̃_t`, integrated over `t ∈ (0,T]`). -/
  w : (Fin n → ℤ) → ℝ≥0∞
  supp : Finset (Fin n → ℤ)
  /-- Markov's threshold (Klartag's `16C₁n⁻²e^{n²T/8}`). -/
  theta : ℝ≥0∞
  theta_ne_zero : theta ≠ 0
  theta_ne_top : theta ≠ ⊤
  /-- Lemma 4.3 through `Tiling.sum_le_lintegral`: twice the first moment is below the threshold. -/
  weight_bound : 2 * (((p - 1 : ℕ) : ℝ≥0∞) * ∑ y ∈ supp, w y)
      < theta * ((p ^ n - 1 : ℕ) : ℝ≥0∞)
  /-- No point in play is `p`-divisible.  `ConstructionA.redMod_ne_zero_of_abs_lt` discharges
  this from a sup-norm bound, i.e. from `p` large. -/
  ball_indivisible : ∀ y : Fin n → ℤ, y ≠ 0 → ‖toE n y‖ ≤ R → redMod p y ≠ 0
  supp_indivisible : ∀ y ∈ supp, redMod p y ≠ 0

/-- **§5's output.**  A single Construction-A line `g` that is simultaneously lattice-free in the
small ball (Klartag's eq. 64) and light in contacts (his eq. 66). -/
theorem exists_good_line_of_chainData [Fact (Nat.Prime p)] [NeZero p] (d : ChainData p n) :
    ∃ g : Fin n → ZMod p, g ≠ 0 ∧
      (∀ y : Fin n → ℤ, y ≠ 0 → ‖toE n y‖ ≤ d.R → y ∉ latZ p n g) ∧
      ∑ y ∈ d.supp.filter (fun y => y ∈ latZ p n g), d.w y < d.theta := by
  classical
  have hp := Fact.out (p := Nat.Prime p)
  have hn := d.dim_pos
  have hnpos : 0 < n := hn
  set A : Finset (Fin n → ℤ) :=
    ((Tiling.finite_ball_integer n d.R).toFinset).filter (fun y => y ≠ 0) with hAdef
  have hAmem : ∀ y, y ∈ A ↔ (‖toE n y‖ ≤ d.R ∧ y ≠ 0) := by
    intro y
    rw [hAdef, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact Iff.rfl
  have hA : ∀ y ∈ A, redMod p y ≠ 0 := by
    intro y hy
    obtain ⟨h1, h2⟩ := (hAmem y).1 hy
    exact d.ball_indivisible y h2 h1
  have hAnorm : ∀ y ∈ A, ‖toE n y‖ ≤ d.R := fun y hy => ((hAmem y).1 hy).1
  have hmpos : 0 < p ^ (n - 1) := pow_pos hp.pos _
  have hAsize : 2 * A.card < p ^ (n - 1) := by
    refine two_mul_card_lt hnpos d.R_nonneg A hAnorm ?_
    have hap := d.alpha_pos
    refine use_one_arith hnpos d.alpha_pos hmpos d.alpha_norm d.R_nonneg
      (by positivity) ?_ d.tiling_defect
    have : d.alpha * (d.R + Real.sqrt n / 2)
        = d.alpha * d.R + d.alpha * Real.sqrt n / 2 := by ring
    rw [this]
    linarith [d.R_scaled]
  obtain ⟨g, hg0, hgfree, hgcontact⟩ :=
    exists_good_line (p := p) hn A d.supp hA d.supp_indivisible d.w d.theta
      d.theta_ne_zero d.theta_ne_top hAsize d.weight_bound
  refine ⟨g, hg0, ?_, ?_⟩
  · intro y hy0 hyR hmem
    exact hgfree y ((hAmem y).2 ⟨hyR, hy0⟩) ((mem_latZ_iff_onLine g y).1 hmem)
  · have hfe : d.supp.filter (fun y => y ∈ latZ p n g)
        = d.supp.filter (fun y => OnLine g (redMod p y)) := by
      exact Finset.filter_congr (fun y _ => mem_latZ_iff_onLine g y)
    rw [hfe]
    exact hgcontact

/-- `p`-indivisibility from a norm bound, pointwise.  This is the pointwise form of
`ConstructionA.redMod_ne_zero_of_abs_lt`, and it is what discharges `ChainData.ball_indivisible`
from `R < p`. -/
theorem redMod_ne_zero_of_norm_lt [NeZero p] {y : Fin n → ℤ} (hy : y ≠ 0)
    (h : ‖Tiling.toE n y‖ < (p : ℝ)) : redMod p y ≠ 0 := by
  intro hzero
  have hdvd : ∀ i, (p : ℤ) ∣ y i := by
    intro i
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (congrFun hzero i)
  obtain ⟨j, hj⟩ : ∃ j, y j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hy (funext hcon)
  have h1 : (p : ℤ) ≤ |y j| := le_abs_of_dvd hdvd hj
  have h2 : |(y j : ℝ)| ≤ ‖Tiling.toE n y‖ := by
    rw [← Tiling.toE_apply]
    exact Tiling.abs_coord_le_norm _ j
  have h3 : ((p : ℤ) : ℝ) ≤ |(y j : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast h1
  push_cast at h3
  linarith

/-- **The interface is satisfiable.**  The four numeric conditions of `ChainData` are jointly
consistent: they build a `ChainData p n` outright (with the Use-2 fields taken trivially — those
are the chain's to supply).  `exists_prime_tiling_defect` below then shows that a prime meeting
`hnorm` and `hdef` exists for every `n ≥ 2`. -/
theorem nonempty_chainData (hn : 1 ≤ n) {p : ℕ} (hp : Nat.Prime p) [NeZero p] {α R : ℝ}
    (hα : 0 < α) (hnorm : α ^ n * ((p ^ (n - 1) : ℕ) : ℝ) = kappa n)
    (hR0 : 0 ≤ R) (hRs : α * R ≤ 1 - 1 / (n : ℝ)) (hRp : R < (p : ℝ))
    (hdef : (n : ℝ) * (α * Real.sqrt n / 2) ≤ 1 / 4) :
    Nonempty (ChainData p n) := by
  have hMpos : 0 < p ^ n - 1 := by
    have h1 : 1 < p ^ n := by
      calc 1 < p := hp.one_lt
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ n := Nat.pow_le_pow_right hp.pos hn
    omega
  exact ⟨{ dim_pos := hn
           alpha := α
           alpha_pos := hα
           alpha_norm := hnorm
           R := R
           R_nonneg := hR0
           R_scaled := hRs
           tiling_defect := hdef
           w := fun _ => 0
           supp := ∅
           theta := 1
           theta_ne_zero := one_ne_zero
           theta_ne_top := ENNReal.one_ne_top
           weight_bound := by
             have hcast : ((0 : ℕ) : ℝ≥0∞) < ((p ^ n - 1 : ℕ) : ℝ≥0∞) := by exact_mod_cast hMpos
             simpa using hcast
           ball_indivisible := fun y hy0 hyR =>
             redMod_ne_zero_of_norm_lt hy0 (lt_of_le_of_lt hyR hRp)
           supp_indivisible := by simp }⟩

/-! ### No `n₀` is needed for §5 -/

/-- For every `n ≥ 2` and every `ε > 0` a prime `p` makes the Klartag scale `α ≤ ε`.
`α = (κ_n / p^{n-1})^{1/n} → 0` as `p → ∞`, and `p` appears nowhere in the conclusion. -/
theorem exists_prime_alpha_le (hn : 2 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℕ, Nat.Prime p ∧ ∃ α : ℝ, 0 < α ∧
      α ^ n * ((p ^ (n - 1) : ℕ) : ℝ) = kappa n ∧ α ≤ ε := by
  have hnpos : 0 < n := by omega
  have hn1 : 1 ≤ n - 1 := by omega
  have hκ : 0 < kappa n := kappa_pos hnpos
  obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes (max 2 ⌈kappa n / ε ^ n⌉₊)
  have hp2 : 2 ≤ p := le_trans (le_max_left _ _) hpge
  have hppos : (0 : ℝ) < p := by positivity
  have hmge : (p : ℝ) ≤ ((p ^ (n - 1) : ℕ) : ℝ) := by
    have : p ^ 1 ≤ p ^ (n - 1) := Nat.pow_le_pow_right (by omega) hn1
    simpa using (by exact_mod_cast this : ((p ^ 1 : ℕ) : ℝ) ≤ ((p ^ (n - 1) : ℕ) : ℝ))
  have hmpos : (0 : ℝ) < ((p ^ (n - 1) : ℕ) : ℝ) := lt_of_lt_of_le hppos hmge
  refine ⟨p, hp, (kappa n / ((p ^ (n - 1) : ℕ) : ℝ)) ^ ((n : ℝ)⁻¹), ?_, ?_, ?_⟩
  · exact Real.rpow_pos_of_pos (by positivity) _
  · rw [Real.rpow_inv_natCast_pow (by positivity) (by omega)]
    field_simp
  · by_contra hcon
    push Not at hcon
    have hαpos : (0 : ℝ) < (kappa n / ((p ^ (n - 1) : ℕ) : ℝ)) ^ ((n : ℝ)⁻¹) :=
      Real.rpow_pos_of_pos (by positivity) _
    have hpow : ε ^ n < ((kappa n / ((p ^ (n - 1) : ℕ) : ℝ)) ^ ((n : ℝ)⁻¹)) ^ n :=
      pow_lt_pow_left₀ hcon hε.le (by omega)
    rw [Real.rpow_inv_natCast_pow (by positivity) (by omega)] at hpow
    have hbound : kappa n / ε ^ n ≤ (p : ℝ) := by
      calc kappa n / ε ^ n ≤ (⌈kappa n / ε ^ n⌉₊ : ℝ) := Nat.le_ceil _
        _ ≤ (p : ℝ) := by
            have : (max 2 ⌈kappa n / ε ^ n⌉₊ : ℕ) ≤ p := hpge
            have h2 : (⌈kappa n / ε ^ n⌉₊ : ℕ) ≤ p := le_trans (le_max_right _ _) this
            exact_mod_cast h2
    have hεn : (0 : ℝ) < ε ^ n := by positivity
    rw [div_le_iff₀ hεn] at hbound
    rw [lt_div_iff₀ hmpos] at hpow
    nlinarith [hmge, hεn, hpow, hbound]

/-- **The tiling defect is always satisfiable.**  For every `n ≥ 2` there is a prime `p` and a
scale `α` meeting `ChainData.alpha_norm` and `ChainData.tiling_defect`.  So §5 imposes **no**
lower bound on `n`: the paper's "n sufficiently large" comes from §§3–4, never from §5. -/
theorem exists_prime_tiling_defect (hn : 2 ≤ n) :
    ∃ p : ℕ, Nat.Prime p ∧ ∃ α : ℝ, 0 < α ∧
      α ^ n * ((p ^ (n - 1) : ℕ) : ℝ) = kappa n ∧
      (n : ℝ) * (α * Real.sqrt n / 2) ≤ 1 / 4 := by
  have hnpos : 0 < n := by omega
  have hnr : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 hnr
  obtain ⟨p, hp, α, hαpos, hαnorm, hαle⟩ :=
    exists_prime_alpha_le hn (ε := 1 / (2 * (n : ℝ) * Real.sqrt n)) (by positivity)
  refine ⟨p, hp, α, hαpos, hαnorm, ?_⟩
  have hkey : (n : ℝ) * (α * Real.sqrt n / 2) ≤ (n : ℝ) * ((1 / (2 * (n : ℝ) * Real.sqrt n)) * Real.sqrt n / 2) := by
    apply mul_le_mul_of_nonneg_left _ hnr.le
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact mul_le_mul_of_nonneg_right hαle hsq.le
  refine le_trans hkey (le_of_eq ?_)
  field_simp
  ring

end Submission.L10.Section5

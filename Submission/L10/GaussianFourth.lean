import Submission.L10.LogDetMartingale

/-!
# Gate L-10 (`klartag_packing`), brief 97 — one Gaussian fourth moment on `UT n`

Report 96b §5 item 3: the centred second moment of `R − h·F` needs `E[‖ξ_k‖⁴] ≤ C·h²·d²` for
`ξ_k = ChainSetup.step c k` (coordinates i.i.d. `gaussianReal 0 (c²)`, `d = Fintype.card (UT n)`),
and the pin has **no moment lemma for `gaussianReal`** — only `mgf_gaussianReal`.

## The route taken, and why

**Not** the layer cake, and **not** the fourth derivative of the moment generating function.  The
cheapest route is the exponential bound directly:

* `y⁴ ≤ 24(e^y + e^{-y})` — the `i = 4` term of `Real.sum_le_exp_of_nonneg` at `|y|`, plus
  `e^{|y|} ≤ e^y + e^{-y}` (`pow_four_le_exp`);
* integrate it at `t·x` and divide by `t⁴`: `E[x⁴] ≤ (24/t⁴)(mgf t + mgf (−t))`, and
  `mgf_fun_id_gaussianReal` evaluates both.  Choosing `t = √(2/v)` makes `v t²/2 = 1`, so the bound
  is `6v² · 2e = 12e·v² ≈ 32.6 v²` — comfortably inside the `C = 100` the caller allows
  (`integral_pow_four_le`).  Integrability comes free from the same domination, against
  `integrable_exp_mul_gaussianReal`.

**No coordinate independence is used.**  `‖ξ‖⁴ = (∑ ξ_p²)² ≤ d·∑ ξ_p⁴` by Chebyshev's sum
inequality (`sq_sum_le_card_mul_sum_sq`), so the cross terms `E[ξ_i²ξ_j²]` the brief anticipated
never appear — which also means the result needs nothing about `iIndepFun`.  The price is the
constant: the sharp value is `h²(d² + 2d)`, this gives `100·h²d²`.

## Contents

`pow_four_le_exp`, `integrable_pow_four_gaussianReal`, `integral_pow_four_le` (the scalar moment),
`norm_sq_eq_sum` and `integral_norm_pow_four_le` (the deliverable on `UT n`).
-/

set_option linter.unusedSectionVars false

namespace Submission.L10.GaussianFourth

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal
open Submission.L10 Submission.L10.Increments

/-! ## 1. The scalar bound -/

/-- **`y⁴ ≤ 24(e^y + e^{-y})`.**  The `i = 4` term of the exponential series at `|y|`. -/
theorem pow_four_le_exp (y : ℝ) : y ^ 4 ≤ 24 * (Real.exp y + Real.exp (-y)) := by
  have habs : |y| ^ 4 = y ^ 4 := by
    rw [← abs_pow, abs_of_nonneg (by positivity)]
  have hser := Real.sum_le_exp_of_nonneg (abs_nonneg y) 5
  have h4 : |y| ^ 4 / (Nat.factorial 4 : ℝ)
      ≤ ∑ i ∈ Finset.range 5, |y| ^ i / (Nat.factorial i : ℝ) := by
    refine Finset.single_le_sum (f := fun i => |y| ^ i / (Nat.factorial i : ℝ)) ?_ ?_
    · intro i _
      positivity
    · simp
  have hfac : (Nat.factorial 4 : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [hfac] at h4
  have hterm : |y| ^ 4 / 24 ≤ Real.exp |y| := le_trans h4 hser
  have hle : Real.exp |y| ≤ Real.exp y + Real.exp (-y) := by
    rcases abs_cases y with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]; linarith [Real.exp_pos (-y)]
    · rw [h]; linarith [Real.exp_pos y]
  rw [← habs]
  linarith

/-- The domination that gives both the integrability and the moment bound. -/
theorem pow_four_le_of_pos {t : ℝ} (ht : 0 < t) (x : ℝ) :
    x ^ 4 ≤ 24 / t ^ 4 * (Real.exp (t * x) + Real.exp (-(t * x))) := by
  have h := pow_four_le_exp (t * x)
  have hexp : (t * x) ^ 4 = t ^ 4 * x ^ 4 := by ring
  rw [hexp] at h
  have ht4 : 0 < t ^ 4 := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ ht4]
  nlinarith [h]

theorem integrable_pow_four_gaussianReal (v : ℝ≥0) :
    Integrable (fun x : ℝ => x ^ 4) (gaussianReal 0 v) := by
  refine Integrable.mono'
    (((integrable_exp_mul_gaussianReal (μ := 0) (v := v) 1).add
      (integrable_exp_mul_gaussianReal (μ := 0) (v := v) (-1))).const_mul (24 / (1 : ℝ) ^ 4))
    (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  have h := pow_four_le_of_pos (t := 1) one_pos x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ x ^ 4)]
  simpa using h

/-- **`E[x⁴] ≤ 100 v²` for `x ~ N(0, v)`.**  The true value is `3v²` and the proof gives
`12e·v² ≈ 32.6 v²`; the caller (report 96b §5) allows anything below `100 v²`. -/
theorem integral_pow_four_le (v : ℝ≥0) :
    ∫ x, x ^ 4 ∂(gaussianReal 0 v) ≤ 100 * (v : ℝ) ^ 2 := by
  rcases eq_or_lt_of_le (v.coe_nonneg) with hv | hv
  · -- `v = 0`: the law is `dirac 0`
    have hv0 : v = 0 := by
      ext
      simpa using hv.symm
    subst hv0
    rw [gaussianReal_zero_var]
    simp
  · set t : ℝ := Real.sqrt (2 / (v : ℝ)) with ht
    have ht0 : 0 < t := by
      rw [ht]
      exact Real.sqrt_pos.2 (by positivity)
    have ht2 : t ^ 2 = 2 / (v : ℝ) := Real.sq_sqrt (by positivity)
    have ht4 : t ^ 4 = 4 / (v : ℝ) ^ 2 := by
      have : t ^ 4 = (t ^ 2) ^ 2 := by ring
      rw [this, ht2, div_pow]
      norm_num
    have hmgf : ∀ s : ℝ, ∫ x, Real.exp (s * x) ∂(gaussianReal 0 v)
        = Real.exp ((v : ℝ) * s ^ 2 / 2) := by
      intro s
      have h := congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := v)) s
      simpa [mgf] using h
    have hdomint : Integrable
        (fun x : ℝ => 24 / t ^ 4 * (Real.exp (t * x) + Real.exp (-(t * x))))
        (gaussianReal 0 v) := by
      have h1 := integrable_exp_mul_gaussianReal (μ := 0) (v := v) t
      have h2 := integrable_exp_mul_gaussianReal (μ := 0) (v := v) (-t)
      have h2' : Integrable (fun x : ℝ => Real.exp (-(t * x))) (gaussianReal 0 v) := by
        simpa [neg_mul] using h2
      exact (h1.add h2').const_mul _
    have hmono : ∫ x, x ^ 4 ∂(gaussianReal 0 v)
        ≤ ∫ x, 24 / t ^ 4 * (Real.exp (t * x) + Real.exp (-(t * x))) ∂(gaussianReal 0 v) := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity)
        hdomint (Filter.Eventually.of_forall fun x => pow_four_le_of_pos ht0 x)
    have hval : ∫ x, 24 / t ^ 4 * (Real.exp (t * x) + Real.exp (-(t * x)))
        ∂(gaussianReal 0 v) = 24 / t ^ 4 * (2 * Real.exp 1) := by
      rw [integral_const_mul]
      have h1 := integrable_exp_mul_gaussianReal (μ := 0) (v := v) t
      have h2 : Integrable (fun x : ℝ => Real.exp (-(t * x))) (gaussianReal 0 v) := by
        simpa [neg_mul] using integrable_exp_mul_gaussianReal (μ := 0) (v := v) (-t)
      rw [integral_add h1 h2]
      have e1 : ∫ x, Real.exp (t * x) ∂(gaussianReal 0 v) = Real.exp 1 := by
        rw [hmgf t, ht2]
        congr 1
        field_simp
      have e2 : ∫ x, Real.exp (-(t * x)) ∂(gaussianReal 0 v) = Real.exp 1 := by
        have : (fun x : ℝ => Real.exp (-(t * x))) = fun x : ℝ => Real.exp ((-t) * x) := by
          funext x; ring_nf
        rw [this, hmgf (-t)]
        congr 1
        rw [neg_pow, ht2]
        norm_num
        field_simp
      rw [e1, e2]
      ring
    rw [hval] at hmono
    refine le_trans hmono ?_
    have hcoef : 24 / t ^ 4 = 6 * (v : ℝ) ^ 2 := by
      rw [ht4]
      field_simp
      ring
    rw [hcoef]
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    nlinarith [he, sq_nonneg ((v : ℝ)), Real.exp_pos 1]

/-! ## 2. The deliverable on `UT n` -/

section Vector

variable {n : ℕ}

theorem norm_sq_eq_sum (x : EuclideanSpace ℝ (UT n)) : ‖x‖ ^ 2 = ∑ p : UT n, (x p) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
  simp [sq]

/-- **`E[‖ξ_k‖⁴] ≤ 100·h²·d²`**, `h = c²`, `d = Fintype.card (UT n)`.  Chebyshev's sum inequality
replaces the cross terms, so no independence of the coordinates is needed. -/
theorem integral_norm_pow_four_le (c : ℝ) (k : ℕ) :
    ∫ ω, ‖ChainSetup.step c k ω‖ ^ 4
        ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))
      ≤ 100 * (c ^ 2) ^ 2 * ((Fintype.card (UT n) : ℝ)) ^ 2 := by
  classical
  have hcoe : ((Real.toNNReal (c ^ 2) : ℝ≥0) : ℝ) = c ^ 2 :=
    Real.coe_toNNReal _ (sq_nonneg c)
  -- each coordinate's fourth moment
  have hcoord : ∀ p : UT n,
      ∫ ω, (ChainSetup.step c k ω p) ^ 4
        ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))
      ≤ 100 * (c ^ 2) ^ 2 := by
    intro p
    have hmeas : AEMeasurable (fun ω : ℕ → EuclideanSpace ℝ (UT n) => ChainSetup.step c k ω p)
        (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) :=
      (StepInputs2.measurable_coord (ChainSetup.measurable_step c k) p).aemeasurable
    have hmap : ∫ ω, (ChainSetup.step c k ω p) ^ 4
        ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))
        = ∫ x, x ^ 4 ∂(gaussianReal 0 (Real.toNNReal (c ^ 2))) := by
      rw [← ChainSetup.step_coord_law c k p]
      refine (integral_map hmeas (f := fun x : ℝ => x ^ 4) ?_).symm
      rw [ChainSetup.step_coord_law c k p]
      fun_prop
    rw [hmap]
    have h := integral_pow_four_le (Real.toNNReal (c ^ 2))
    rwa [hcoe] at h
  have hintcoord : ∀ p : UT n, Integrable
      (fun ω : ℕ → EuclideanSpace ℝ (UT n) => (ChainSetup.step c k ω p) ^ 4)
      (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) := by
    intro p
    have hmeas : AEMeasurable (fun ω : ℕ → EuclideanSpace ℝ (UT n) => ChainSetup.step c k ω p)
        (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) :=
      (StepInputs2.measurable_coord (ChainSetup.measurable_step c k) p).aemeasurable
    have hg : AEStronglyMeasurable (fun x : ℝ => x ^ 4)
        (Measure.map (fun ω : ℕ → EuclideanSpace ℝ (UT n) => ChainSetup.step c k ω p)
          (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))) := by
      rw [ChainSetup.step_coord_law c k p]
      fun_prop
    have hiff := integrable_map_measure hg hmeas
    rw [ChainSetup.step_coord_law c k p] at hiff
    exact hiff.1 (integrable_pow_four_gaussianReal _)
  -- the pointwise Chebyshev bound
  have hpt : ∀ ω : ℕ → EuclideanSpace ℝ (UT n),
      ‖ChainSetup.step c k ω‖ ^ 4
        ≤ (Fintype.card (UT n) : ℝ) * ∑ p : UT n, (ChainSetup.step c k ω p) ^ 4 := by
    intro ω
    have h1 : ‖ChainSetup.step c k ω‖ ^ 4
        = (∑ p : UT n, (ChainSetup.step c k ω p) ^ 2) ^ 2 := by
      rw [← norm_sq_eq_sum]
      ring
    have h2 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (UT n)))
      (f := fun p => (ChainSetup.step c k ω p) ^ 2)
    rw [h1]
    refine le_trans h2 (le_of_eq ?_)
    rw [Finset.card_univ]
    refine congrArg _ (Finset.sum_congr rfl fun p _ => ?_)
    ring
  refine le_trans (integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun ω => by positivity)
    (((integrable_finsetSum _ fun p _ => hintcoord p).const_mul
      ((Fintype.card (UT n) : ℝ))))
    (Filter.Eventually.of_forall hpt)) ?_
  rw [integral_const_mul, integral_finsetSum _ fun p _ => hintcoord p]
  have hsum : ∑ _p : UT n, (100 * (c ^ 2) ^ 2) = (Fintype.card (UT n) : ℝ) * (100 * (c ^ 2) ^ 2) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hle : ∑ p : UT n, ∫ ω, (ChainSetup.step c k ω p) ^ 4
        ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))
      ≤ (Fintype.card (UT n) : ℝ) * (100 * (c ^ 2) ^ 2) := by
    rw [← hsum]
    exact Finset.sum_le_sum fun p _ => hcoord p
  have hd0 : (0 : ℝ) ≤ (Fintype.card (UT n) : ℝ) := Nat.cast_nonneg _
  nlinarith [hle, hd0]

/-- **The conditional form (brief 97 item (iv))**: `ξ_k` is independent of `ℱ_k`
(`ChainSetup.indep_step_natFil`), so the conditional fourth moment is the unconditional one and
`integral_norm_pow_four_le` bounds it. -/
theorem condExp_norm_pow_four (c : ℝ) (k : ℕ) :
    (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))[
        fun ω => ‖ChainSetup.step c k ω‖ ^ 4
        | ChainSetup.filtration (F := EuclideanSpace ℝ (UT n)) k]
      =ᵐ[ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))] fun _ =>
        ∫ ω, ‖ChainSetup.step c k ω‖ ^ 4
          ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) := by
  refine condExp_indep_eq (ChainSetup.measurable_step c k).comap_le
    (ChainSetup.natFil_le k) ?_ (ChainSetup.indep_step_natFil c k)
  have hmeas : Measurable[MeasurableSpace.comap
      (fun ω : ℕ → EuclideanSpace ℝ (UT n) => ChainSetup.step c k ω) inferInstance]
      (fun ω : ℕ → EuclideanSpace ℝ (UT n) => ‖ChainSetup.step c k ω‖ ^ 4) :=
    (measurable_norm.comp (comap_measurable _)).pow_const 4
  exact hmeas.stronglyMeasurable

end Vector

end Submission.L10.GaussianFourth

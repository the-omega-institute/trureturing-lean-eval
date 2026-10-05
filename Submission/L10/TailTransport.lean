/-
Gate L-10 (`klartag_packing`), brief 42.

**The transport: Proposition 4.1 at step `k` as a statement about the chain's own measure.**

Report 40 left one line: `padded_tail_of_increments` at `N := k` concludes on
`Ω₁ × (Fin k → ℝ)`, a different space for each step.  The transport is cheap, and `Padding.lean`'s
own docstring says why: **`hitSet M N` depends only on the chain.**  It is the cylinder
`{ω₁ | ∃ j ≤ N, M j ω₁ ≤ 0} ×ˢ univ`, so the padding factor integrates out against a probability
measure and the bound is a bound on `P₁` alone (§1).  The padding dimension therefore never leaves
the proof of Proposition 4.1, and no `k`-indexed family of spaces survives into §3's hypothesis.

What the chain still owes is `hincl` — that the padded increment vector is i.i.d. `N(0,δ)` — and §2
gives its reusable half: independence across steps plus a common Gaussian law is exactly the
product law on `Fin k → ℝ`.
-/
import Submission.L10.TailAtStep
import Submission.L10.Padding
import Submission.L10.StepGlue

namespace Submission.L10

open MeasureTheory ProbabilityTheory Set Real Submission.L10.ChainDataInst Submission.L10.Tiling
open scoped ENNReal NNReal

/-! ## 1. The hitting event is a cylinder: the padding integrates out -/

/-- **The transport.**  `hitSet M N` does not read the padding coordinates, so its probability
under the padded measure is its probability under the chain's measure. -/
theorem measure_hitSet_fst {Ω₁ : Type*} [MeasurableSpace Ω₁] {P₁ : Measure Ω₁} [SFinite P₁]
    {N : ℕ} {ν : Measure ℝ} [IsProbabilityMeasure ν] (M : ℕ → Ω₁ → ℝ) :
    (P₁.prod (Measure.pi fun _ : Fin N => ν)) (hitSet M N)
      = P₁ {ω₁ | ∃ k ≤ N, M k ω₁ ≤ 0} := by
  have hset : hitSet M N
      = ({ω₁ | ∃ k ≤ N, M k ω₁ ≤ 0} ×ˢ (Set.univ : Set (Fin N → ℝ))) := by
    ext ω; simp [hitSet, Set.mem_prod]
  rw [hset, Measure.prod_prod, measure_univ, mul_one]

/-- **Proposition 4.1 at horizon `t`, about the chain's measure alone.**  `Klartag`'s `M₀` is the
initial gap `a₀ − (α·r)⁻²` and `q = 1`, so the tail's argument is `yOf a₀ t (α·r)` — the profile's
own argument, by `TailAtStep.tail_arg_eq`. -/
theorem hit_tail_yOf {Ω₁ : Type*} [MeasurableSpace Ω₁] {P₁ : Measure Ω₁}
    [IsProbabilityMeasure P₁] {k : ℕ} {δ : ℝ≥0} {M c : ℕ → Ω₁ → ℝ}
    (hM : ∀ j, Measurable (M j)) (hc : ∀ i, Measurable (c i))
    {a₀ u t : ℝ} (ht : 0 < t) (hM₀ : 0 < a₀ - (u ^ 2)⁻¹)
    (hv : (((k • δ : ℝ≥0)) : ℝ) = t * 1 ^ 2)
    {inc : (Ω₁ × (Fin k → ℝ)) → (Fin k → ℝ)} (hincm : Measurable inc)
    (hincw : ∀ j : ℕ, j ≤ k → ∀ ω : Ω₁ × (Fin k → ℝ),
      walkSum j (inc ω) = -(paddedProc M (a₀ - (u ^ 2)⁻¹) c j ω))
    (hincl : (P₁.prod (Measure.pi fun _ : Fin k => gaussianReal 0 δ)).map inc
      = Measure.pi fun _ : Fin k => gaussianReal 0 δ) :
    P₁ {ω₁ | ∃ j ≤ k, M j ω₁ ≤ 0} ≤ ENNReal.ofReal (4 * Phi (yOf a₀ t u)) := by
  have h := padded_tail_of_increments hM hc ht one_pos hM₀ hv hincm hincw hincl
  rw [measure_hitSet_fst, tail_arg_eq] at h
  exact h

/-! ## 2. `hincl`'s reusable half: independence plus a common law is the product law -/

/-- **The `Fin k` product law.**  If the chain's first `k` scalar increments are independent and
each `N(0,δ)`, the vector they form has exactly the padding law.  This is what `hincl` needs about
the chain; the remaining content of `hincl` is that the padding construction's `inc` *is* that
vector, which is the construction's own definition. -/
theorem map_pi_of_iIndep {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {k : ℕ} {δ : ℝ≥0} (X : Fin k → Ω → ℝ)
    (hm : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hlaw : ∀ i, μ.map (X i) = gaussianReal 0 δ) :
    μ.map (fun ω i => X i ω) = Measure.pi fun _ : Fin k => gaussianReal 0 δ := by
  rw [(iIndepFun_iff_map_fun_eq_pi_map (fun i => (hm i).aemeasurable)).1 hind]
  simp only [hlaw]

/-- **The currency conversion.**  A scalar increment read in a *frozen* direction — the direction
is a function of the past, so `Increments.map_frozen_isometry` applies — is `N(0, r²)` after the
chain's scaling `r`.  With `r = √h` this is the `δ = h` that `padded_tail_of_increments` asks for
through its `hv`. -/
theorem map_frozen_coord {Ω α : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] [MeasurableSpace α] {ι : Type*} [Fintype ι]
    {Z : Ω → α} {ξ : Ω → EuclideanSpace ℝ ι} (hZ : Measurable Z) (hξ : Measurable ξ)
    (hindep : IndepFun Z ξ P) (hlaw : P.map ξ = stdGaussian (EuclideanSpace ℝ ι))
    (U : α → (EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι))
    (hU : Measurable fun q : α × EuclideanSpace ℝ ι => U q.1 q.2) (r : ℝ) (p : ι) :
    P.map (fun ω => (r • U (Z ω) (ξ ω)) p) = gaussianReal 0 (Real.toNNReal (r ^ 2)) :=
  StepGlue.coord_law_smul (hU.comp (hZ.prodMk hξ))
    (Increments.map_frozen_isometry hZ hξ hindep hlaw U hU) r p

/-! ## 3. The per-step tail, about `μ` alone -/

/-- **`tail_at_step_μ`.**  The hypothesis `ContactIntegrated.integrated_count_le`,
`ContactIntegrated.sum_free_ge` and `ChainRaw2` all consume, stated on the chain's measure with no
padding space in sight.

`hhit` is the containment the chain's freezing supplies: a point contacted by step `k` has had its
martingale reach the boundary by step `k`.  `hprop` is `hit_tail_yOf` at horizon `k·h`, one
instance per point and step.  `hzero` is `padded_tail_of_increments`' own `hM₀ : 0 < M₀`, read at
`k = 0`: `hitSet M 0 = {M₀ ≤ 0}` is empty. -/
theorem tail_at_step_μ {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} {α hstep : ℝ} {N : ℕ} (C : ℕ → Ω → Finset (Fin n → ℤ))
    (W : Finset (Fin n → ℤ)) (M : (Fin n → ℤ) → ℕ → Ω → ℝ)
    (hwin : ∀ y ∈ W, ‖toE n y‖ + Real.sqrt n / 2 ≤ windowC α n)
    (hr : ∀ y ∈ W, 0 < α * ‖toE n y‖)
    (hy : ∀ k, k < N → k ≠ 0 → ∀ y ∈ W,
      0 < yOf (a0C n) ((k : ℝ) * hstep) (α * ‖toE n y‖))
    (hhit : ∀ k, k < N → ∀ y ∈ W,
      {ω | y ∈ C k ω} ⊆ {ω | ∃ j ≤ k, M y j ω ≤ 0})
    (hprop : ∀ k, k < N → k ≠ 0 → ∀ y ∈ W,
      μ {ω | ∃ j ≤ k, M y j ω ≤ 0}
        ≤ ENNReal.ofReal (4 * Phi (yOf (a0C n) ((k : ℝ) * hstep) (α * ‖toE n y‖))))
    (hzero : ∀ y ∈ W, μ.real {ω | y ∈ C 0 ω} = 0) :
    ∀ k, k < N → ∀ y ∈ W,
      μ.real {ω | y ∈ C k ω}
        ≤ 4 * profStep α n hstep y k := by
  refine tail_at_step C W hwin hr hy ?_ hzero
  intro k hk hk0 y hy'
  exact le_trans (measure_mono (hhit k hk y hy')) (hprop k hk hk0 y hy')

/-- The same, folded into `profStep`'s definition — the literal shape `ChainRaw2.tail` is proved
from, through `TailAtStep.tail_of_steps`. -/
theorem tail_of_transport {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} {α : ℝ} (hn : 3 ≤ n) (hα : 0 < α)
    (C : ℕ → Ω → Finset (Fin n → ℤ)) (W : Finset (Fin n → ℤ))
    (M : (Fin n → ℤ) → ℕ → Ω → ℝ)
    (hwin : ∀ y ∈ W, ‖toE n y‖ + Real.sqrt n / 2 ≤ windowC α n)
    (hr : ∀ y ∈ W, 0 < α * ‖toE n y‖)
    (hy : ∀ k, k < ParamsAdopted2.numStepsAdopted2 n → k ≠ 0 → ∀ y ∈ W,
      0 < yOf (a0C n) ((k : ℝ) * ParamsAdopted2.stepSizeAdopted2 n) (α * ‖toE n y‖))
    (hhit : ∀ k, k < ParamsAdopted2.numStepsAdopted2 n → ∀ y ∈ W,
      {ω | y ∈ C k ω} ⊆ {ω | ∃ j ≤ k, M y j ω ≤ 0})
    (hprop : ∀ k, k < ParamsAdopted2.numStepsAdopted2 n → k ≠ 0 → ∀ y ∈ W,
      μ {ω | ∃ j ≤ k, M y j ω ≤ 0}
        ≤ ENNReal.ofReal (4 * Phi (yOf (a0C n)
            ((k : ℝ) * ParamsAdopted2.stepSizeAdopted2 n) (α * ‖toE n y‖))))
    (hzero : ∀ y ∈ W, μ.real {ω | y ∈ C 0 ω} = 0) :
    ∀ y ∈ W, ENNReal.ofReal (ContactIntegrated.intWeight μ C
        (ParamsAdopted2.stepSizeAdopted2 n) (ParamsAdopted2.numStepsAdopted2 n) y)
      ≤ ENNReal.ofReal (4 * ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
          profileAt (a0C n) α (windowC α n) n t ‖toE n y‖) :=
  fun y hy' => tail_of_steps hn hα C
    (fun k hk => tail_at_step_μ C W M hwin hr hy hhit hprop hzero k hk y hy')

end Submission.L10

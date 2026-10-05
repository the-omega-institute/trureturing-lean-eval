/-
Gate L-10 (`klartag_packing`), brief 43.

**The padding map, and `hincl` at every horizon.**

Report 42 named the obstruction: the chain's scalar increments `⟪π_k ξ_k, v_k⟫` have a
*past-dependent* variance `h‖π_k v_k‖²`, so they are a martingale-difference sequence and not an
independent one.  Klartag's fix is to pad each with an independent Gaussian of variance
`h(1 − ‖π_k v_k‖²)`.

**In vector form the padding is one inner product.**  Writing `w = π_k v_k` and letting `e` be a
fresh unit direction orthogonal to `w`, the padded increment is `√h·⟪ξ_k, u_k⟫` with
`u_k = w + √(1 − ‖w‖²)·e` a **unit** vector (`norm_padUnit`).  So the whole construction is: read
the fresh Gaussian in a past-measurable unit direction.

Three consequences, and none of them needs a measurable rotation:

* `map_inner_stdGaussian` — a linear functional of a standard Gaussian is `N(0,‖v‖²)`, by
  characteristic functions; at a unit vector, `N(0,1)`.
* `map_frozen` / `indepFun_frozen` — `Increments.map_frozen_isometry` generalised from families of
  *isometries* to any measurable family whose fibre law does not depend on the parameter.  This is
  what makes the rotation unnecessary: only the constancy of the law is used.
* `map_pi_of_stepIndep` — a sequence each of whose terms is independent of its own past and has a
  fixed law is i.i.d.; this is `hincl` at every horizon.
-/
import Submission.L10.TailTransport
import Submission.L10.Increments

namespace Submission.L10

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal NNReal RealInnerProductSpace

/-! ## 1. A linear functional of a standard Gaussian, and the padding direction -/

theorem map_inner_stdGaussian {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] (v : F) :
    (stdGaussian F).map (fun x => ⟪x, v⟫) = gaussianReal 0 (Real.toNNReal (‖v‖ ^ 2)) := by
  refine Measure.ext_of_charFun ?_
  funext t
  rw [Increments.charFun_map_of_inner (stdGaussian F) (fun x => ⟪x, v⟫) (by fun_prop)
      (fun s : ℝ => s • v) (fun x s => by
        simp [real_inner_smul_right, real_inner_comm]),
    charFun_stdGaussian, charFun_gaussianReal]
  congr 1
  have hn : ‖t • v‖ = |t| * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs]
  have hreal : (|t| * ‖v‖) ^ 2 = ‖v‖ ^ 2 * t ^ 2 := by rw [mul_pow, sq_abs]; ring
  rw [hn, Real.coe_toNNReal _ (sq_nonneg _), ← Complex.ofReal_pow, hreal]
  push_cast
  ring

/-- **The padding direction is a unit vector.**  `w` is the projected drift direction `π_k v_k`,
`e` a fresh direction orthogonal to it; `√(1 − ‖w‖²)` is Klartag's padding amplitude, and the
Pythagorean identity is exactly the statement that the padded conditional variance is `h`. -/
theorem norm_padUnit {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {w e : F}
    (hw : ‖w‖ ≤ 1) (he : ‖e‖ = 1) (horth : ⟪w, e⟫ = 0) :
    ‖w + Real.sqrt (1 - ‖w‖ ^ 2) • e‖ = 1 := by
  have hnn : (0 : ℝ) ≤ 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  have horth' : ⟪w, Real.sqrt (1 - ‖w‖ ^ 2) • e⟫ = 0 := by
    rw [real_inner_smul_right, horth, mul_zero]
  have hpy : ‖w + Real.sqrt (1 - ‖w‖ ^ 2) • e‖ ^ 2
      = ‖w‖ ^ 2 + ‖Real.sqrt (1 - ‖w‖ ^ 2) • e‖ ^ 2 := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_real horth'
    simpa only [← pow_two] using h
  have hs : ‖Real.sqrt (1 - ‖w‖ ^ 2) • e‖ ^ 2 = 1 - ‖w‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, he, mul_one, sq_abs, Real.sq_sqrt hnn]
  have h1 : ‖w + Real.sqrt (1 - ‖w‖ ^ 2) • e‖ ^ 2 = 1 := by rw [hpy, hs]; ring
  nlinarith [norm_nonneg (w + Real.sqrt (1 - ‖w‖ ^ 2) • e)]

/-- The padded increment's law at a *fixed* unit direction: `N(0, r²)`. -/
theorem map_scaled_inner {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] {u : F} (hu : ‖u‖ = 1) (r : ℝ) :
    (stdGaussian F).map (fun g => r * ⟪g, u⟫) = gaussianReal 0 (Real.toNNReal (r ^ 2)) := by
  rw [show (fun g : F => r * ⟪g, u⟫) = (fun t : ℝ => r * t) ∘ (fun g : F => ⟪g, u⟫) from rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop), map_inner_stdGaussian, hu,
    show (fun t : ℝ => r * t) = (r * ·) from rfl, gaussianReal_map_const_mul]
  refine gaussianReal_ext_iff.2 ⟨by ring, ?_⟩
  refine NNReal.coe_injective ?_
  rw [NNReal.coe_mul, Real.coe_toNNReal _ (sq_nonneg r), Real.coe_toNNReal _ (by norm_num)]
  norm_num

/-! ## 2. The frozen family: the rotation is not needed, only constancy of the fibre law -/

theorem map_prod_frozen {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace E] (μ : Measure α) [SFinite μ] {ρ : Measure E} [SFinite ρ]
    {ν : Measure β} [SFinite ν]
    (F : α → E → β) (hF : Measurable fun q : α × E => F q.1 q.2)
    (hfib : ∀ a, ρ.map (F a) = ν) :
    (μ.prod ρ).map (fun q => (q.1, F q.1 q.2)) = μ.prod ν := by
  have hmeas : Measurable fun q : α × E => (q.1, F q.1 q.2) := measurable_fst.prodMk hF
  have hFa : ∀ a, Measurable (F a) := fun a => hF.comp (measurable_const.prodMk measurable_id)
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply hmeas hs, Measure.prod_apply (hmeas hs), Measure.prod_apply hs]
  refine lintegral_congr fun a => ?_
  have hpre : (Prod.mk a ⁻¹' ((fun q : α × E => (q.1, F q.1 q.2)) ⁻¹' s))
      = (F a) ⁻¹' (Prod.mk a ⁻¹' s) := rfl
  rw [hpre, ← Measure.map_apply (hFa a) (measurable_prodMk_left hs), hfib a]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem map_prod_eq_frozen {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace E] {Z : Ω → α} {ξ : Ω → E} (hZ : Measurable Z) (hξ : Measurable ξ)
    (hindep : IndepFun Z ξ P) {ρ : Measure E} [SFinite ρ] {ν : Measure β} [SFinite ν]
    (hlaw : P.map ξ = ρ) (F : α → E → β) (hF : Measurable fun q : α × E => F q.1 q.2)
    (hfib : ∀ a, ρ.map (F a) = ν) :
    P.map (fun ω => (Z ω, F (Z ω) (ξ ω))) = (P.map Z).prod ν := by
  have hpair : P.map (fun ω => (Z ω, ξ ω)) = (P.map Z).prod ρ := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hZ.aemeasurable hξ.aemeasurable).1 hindep, hlaw]
  have hcomp : (fun ω => (Z ω, F (Z ω) (ξ ω)))
      = (fun q : α × E => (q.1, F q.1 q.2)) ∘ (fun ω => (Z ω, ξ ω)) := rfl
  rw [hcomp, ← Measure.map_map (measurable_fst.prodMk hF) (hZ.prodMk hξ), hpair,
    map_prod_frozen _ F hF hfib]

/-- **The frozen law.**  `Increments.map_frozen_isometry` with the isometry hypothesis weakened to
constancy of the fibre law. -/
theorem map_frozen {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace E] {Z : Ω → α} {ξ : Ω → E} (hZ : Measurable Z) (hξ : Measurable ξ)
    (hindep : IndepFun Z ξ P) {ρ : Measure E} [SFinite ρ] {ν : Measure β}
    [IsProbabilityMeasure ν] (hlaw : P.map ξ = ρ) (F : α → E → β)
    (hF : Measurable fun q : α × E => F q.1 q.2) (hfib : ∀ a, ρ.map (F a) = ν) :
    P.map (fun ω => F (Z ω) (ξ ω)) = ν := by
  have hmeas : Measurable fun ω => F (Z ω) (ξ ω) := hF.comp (hZ.prodMk hξ)
  have hPZ : IsProbabilityMeasure (P.map Z) :=
    ⟨by rw [Measure.map_apply hZ MeasurableSet.univ, Set.preimage_univ, measure_univ]⟩
  have h := map_prod_eq_frozen hZ hξ hindep hlaw F hF hfib
  have hsnd : P.map (fun ω => F (Z ω) (ξ ω))
      = (P.map (fun ω => (Z ω, F (Z ω) (ξ ω)))).map Prod.snd := by
    rw [Measure.map_map measurable_snd (hZ.prodMk hmeas)]; rfl
  rw [hsnd, h, Measure.map_snd_prod, measure_univ, one_smul]

/-- **The frozen independence.**  The padded increment is independent of the past it was read
against. -/
theorem indepFun_frozen {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace E] {Z : Ω → α} {ξ : Ω → E} (hZ : Measurable Z) (hξ : Measurable ξ)
    (hindep : IndepFun Z ξ P) {ρ : Measure E} [SFinite ρ] {ν : Measure β}
    [IsProbabilityMeasure ν] (hlaw : P.map ξ = ρ) (F : α → E → β)
    (hF : Measurable fun q : α × E => F q.1 q.2) (hfib : ∀ a, ρ.map (F a) = ν) :
    IndepFun Z (fun ω => F (Z ω) (ξ ω)) P := by
  have hmeas : Measurable fun ω => F (Z ω) (ξ ω) := hF.comp (hZ.prodMk hξ)
  rw [indepFun_iff_map_prod_eq_prod_map_map hZ.aemeasurable hmeas.aemeasurable,
    map_prod_eq_frozen hZ hξ hindep hlaw F hF hfib, map_frozen hZ hξ hindep hlaw F hF hfib]

/-! ## 3. Independent of its own past, with a fixed law, implies i.i.d. -/

/-- **`hincl` at every horizon.**  The induction is on the horizon: the pair
`(X k, (X i)_{i<k})` has law `ν ⊗ πν` by independence, and `Fin.insertNthEquiv` at `Fin.last k`
turns `ν ⊗ πν` into `π ν` on `Fin (k+1)`. -/
theorem map_pi_of_stepIndep {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (X : ℕ → Ω → ℝ) (hm : ∀ i, Measurable (X i))
    (hlaw : ∀ i, P.map (X i) = ν)
    (hind : ∀ k, IndepFun (X k) (fun ω (i : Fin k) => X (i : ℕ) ω) P) (k : ℕ) :
    P.map (fun ω (i : Fin k) => X (i : ℕ) ω) = Measure.pi (fun _ : Fin k => ν) := by
  induction k with
  | zero =>
    refine Measure.ext fun s hs => ?_
    rcases Set.eq_empty_or_nonempty s with rfl | ⟨x, hx⟩
    · simp
    · have hsu : s = Set.univ := by
        ext y
        simp only [Set.mem_univ, iff_true]
        have hy : y = x := Subsingleton.elim _ _
        rw [hy]; exact hx
      have h1 : IsProbabilityMeasure (P.map (fun ω (i : Fin 0) => X (i : ℕ) ω)) :=
        ⟨by rw [Measure.map_apply (by fun_prop) MeasurableSet.univ, Set.preimage_univ,
          measure_univ]⟩
      rw [hsu, measure_univ, measure_univ]
  | succ k ih =>
    have hmpast : Measurable (fun ω (i : Fin k) => X (i : ℕ) ω) :=
      Measurable.of_eval (fun i => hm i)
    have hmall : Measurable (fun ω (j : Fin (k + 1)) => X (j : ℕ) ω) :=
      Measurable.of_eval (fun j => hm j)
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) (Fin.last k) with he
    have hpair : P.map (fun ω => (X k ω, fun i : Fin k => X (i : ℕ) ω))
        = ν.prod (Measure.pi fun _ : Fin k => ν) := by
      rw [(indepFun_iff_map_prod_eq_prod_map_map (hm k).aemeasurable
        hmpast.aemeasurable).1 (hind k), hlaw k, ih]
    have hcomp : (fun ω => (X k ω, fun i : Fin k => X (i : ℕ) ω))
        = (fun f : Fin (k + 1) → ℝ => e f) ∘ (fun ω (j : Fin (k + 1)) => X (j : ℕ) ω) := by
      funext ω
      simp [he, MeasurableEquiv.piFinSuccAbove, Fin.val_last]
      funext i
      rfl
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => ν) (Fin.last k)
    have hsym : (ν.prod (Measure.pi fun _ : Fin k => ν)).map e.symm
        = Measure.pi (fun _ : Fin (k + 1) => ν) := (MeasurePreserving.symm _ hmp).map_eq
    have hA : P.map (fun ω (j : Fin (k + 1)) => X (j : ℕ) ω)
        = ((P.map (fun ω (j : Fin (k + 1)) => X (j : ℕ) ω)).map e).map e.symm := by
      rw [Measure.map_map e.symm.measurable e.measurable, MeasurableEquiv.symm_comp_self,
        Measure.map_id]
    rw [hcomp, ← Measure.map_map e.measurable hmall] at hpair
    rw [hA, hpair, hsym]

/-! ## 4. The padding map itself -/

section PaddingMap

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- The past of the increments — `StateInvariant3.past`, at a general carrier. -/
def pastOf (ξ : ℕ → Ω → F) (k : ℕ) (ω : Ω) : ℕ → F := fun j => if j < k then ξ j ω else 0

/-- **The padding map.**  The `k`-th padded increment is the fresh Gaussian read in a
past-measurable **unit** direction; `norm_padUnit` is what makes that direction a unit vector, and
hence the conditional variance exactly `r²`. -/
noncomputable def padInc (r : ℝ) (ξ : ℕ → Ω → F) (u : ℕ → (ℕ → F) → F) (k : ℕ) (ω : Ω) : ℝ :=
  r * ⟪ξ k ω, u k (pastOf ξ k ω)⟫

omit [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [BorelSpace F] in
theorem measurable_pastOf {ξ : ℕ → Ω → F} (hξ : ∀ j, Measurable (ξ j)) (k : ℕ) :
    Measurable (pastOf ξ k) := by
  refine Measurable.of_eval fun j => ?_
  show Measurable fun ω => if j < k then ξ j ω else (0 : F)
  by_cases h : j < k
  · simp only [ite_eq_left h]; exact hξ j
  · simp only [ite_eq_right h]; exact measurable_const

theorem measurable_padInc {r : ℝ} {ξ : ℕ → Ω → F} {u : ℕ → (ℕ → F) → F}
    (hξ : ∀ j, Measurable (ξ j)) (hu : ∀ k, Measurable (u k)) (k : ℕ) :
    Measurable (padInc r ξ u k) :=
  measurable_const.mul (continuous_inner.measurable.comp
    ((hξ k).prodMk ((hu k).comp (measurable_pastOf hξ k))))

/-- **The padded increment is `N(0, r²)`** — uniformly in the past. -/
theorem map_padInc {r : ℝ} {ξ : ℕ → Ω → F} {u : ℕ → (ℕ → F) → F}
    (hξ : ∀ j, Measurable (ξ j)) (hu : ∀ k, Measurable (u k))
    (hlaw : ∀ k, P.map (ξ k) = stdGaussian F)
    (hpast : ∀ k, IndepFun (pastOf ξ k) (ξ k) P)
    (hunit : ∀ k p, ‖u k p‖ = 1) (k : ℕ) :
    P.map (padInc r ξ u k) = gaussianReal 0 (Real.toNNReal (r ^ 2)) :=
  map_frozen (measurable_pastOf hξ k) (hξ k) (hpast k) (hlaw k)
    (fun p g => r * ⟪g, u k p⟫)
    (measurable_const.mul (continuous_inner.measurable.comp
      (measurable_snd.prodMk ((hu k).comp measurable_fst))))
    (fun p => map_scaled_inner (hunit k p) r)

/-- …and independent of the past it was read against. -/
theorem indepFun_padInc {r : ℝ} {ξ : ℕ → Ω → F} {u : ℕ → (ℕ → F) → F}
    (hξ : ∀ j, Measurable (ξ j)) (hu : ∀ k, Measurable (u k))
    (hlaw : ∀ k, P.map (ξ k) = stdGaussian F)
    (hpast : ∀ k, IndepFun (pastOf ξ k) (ξ k) P)
    (hunit : ∀ k p, ‖u k p‖ = 1) (k : ℕ) :
    IndepFun (pastOf ξ k) (padInc r ξ u k) P :=
  indepFun_frozen (measurable_pastOf hξ k) (hξ k) (hpast k) (hlaw k)
    (fun p g => r * ⟪g, u k p⟫)
    (measurable_const.mul (continuous_inner.measurable.comp
      (measurable_snd.prodMk ((hu k).comp measurable_fst))))
    (fun p => map_scaled_inner (hunit k p) r)

/-- The first `k` padded increments, as a function of the past alone. -/
noncomputable def padVec (r : ℝ) (u : ℕ → (ℕ → F) → F) (k : ℕ) (p : ℕ → F) : Fin k → ℝ :=
  fun i => r * ⟪p (i : ℕ), u (i : ℕ) (fun j => if j < (i : ℕ) then p j else 0)⟫

theorem measurable_padVec {r : ℝ} {u : ℕ → (ℕ → F) → F} (hu : ∀ k, Measurable (u k)) (k : ℕ) :
    Measurable (padVec r u k) := by
  refine Measurable.of_eval fun i => ?_
  refine measurable_const.mul (continuous_inner.measurable.comp
    ((measurable_pi_apply (i : ℕ)).prodMk ((hu (i : ℕ)).comp ?_)))
  refine Measurable.of_eval fun j => ?_
  by_cases h : j < (i : ℕ)
  · simp only [ite_eq_left h]; exact measurable_pi_apply j
  · simp only [ite_eq_right h]; exact measurable_const

omit [MeasurableSpace Ω] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
theorem padVec_pastOf (r : ℝ) (ξ : ℕ → Ω → F) (u : ℕ → (ℕ → F) → F) (k : ℕ) (ω : Ω) :
    padVec r u k (pastOf ξ k ω) = fun i : Fin k => padInc r ξ u (i : ℕ) ω := by
  funext i
  have h1 : pastOf ξ k ω (i : ℕ) = ξ (i : ℕ) ω := ite_eq_left i.isLt
  have h2 : (fun j => if j < (i : ℕ) then pastOf ξ k ω j else 0) = pastOf ξ (i : ℕ) ω := by
    funext j
    by_cases hj : j < (i : ℕ)
    · show (if j < (i : ℕ) then (if j < k then ξ j ω else 0) else 0)
        = if j < (i : ℕ) then ξ j ω else 0
      rw [ite_eq_left hj, ite_eq_left hj, ite_eq_left (lt_trans hj i.isLt)]
    · show (if j < (i : ℕ) then (if j < k then ξ j ω else 0) else 0)
        = if j < (i : ℕ) then ξ j ω else 0
      rw [ite_eq_right hj, ite_eq_right hj]
  show r * ⟪pastOf ξ k ω (i : ℕ), u (i : ℕ) (fun j => if j < (i : ℕ) then pastOf ξ k ω j else 0)⟫
    = padInc r ξ u (i : ℕ) ω
  rw [h1, h2]; rfl

theorem indepFun_padInc_past {r : ℝ} {ξ : ℕ → Ω → F} {u : ℕ → (ℕ → F) → F}
    (hξ : ∀ j, Measurable (ξ j)) (hu : ∀ k, Measurable (u k))
    (hlaw : ∀ k, P.map (ξ k) = stdGaussian F)
    (hpast : ∀ k, IndepFun (pastOf ξ k) (ξ k) P)
    (hunit : ∀ k p, ‖u k p‖ = 1) (k : ℕ) :
    IndepFun (padInc r ξ u k) (fun ω (i : Fin k) => padInc r ξ u (i : ℕ) ω) P := by
  have h := (indepFun_padInc (r := r) hξ hu hlaw hpast hunit k).symm
  have h2 := h.comp (measurable_id : Measurable (id : ℝ → ℝ)) (measurable_padVec (r := r) hu k)
  have hfun : (fun ω => padVec r u k (pastOf ξ k ω))
      = fun ω (i : Fin k) => padInc r ξ u (i : ℕ) ω := by
    funext ω; exact padVec_pastOf r ξ u k ω
  simpa [Function.comp_def, hfun] using h2

/-- **`hincl` at every horizon.**  The padded increments are i.i.d. `N(0, r²)`. -/
theorem hincl_of_padding {r : ℝ} {ξ : ℕ → Ω → F} {u : ℕ → (ℕ → F) → F}
    (hξ : ∀ j, Measurable (ξ j)) (hu : ∀ k, Measurable (u k))
    (hlaw : ∀ k, P.map (ξ k) = stdGaussian F)
    (hpast : ∀ k, IndepFun (pastOf ξ k) (ξ k) P)
    (hunit : ∀ k p, ‖u k p‖ = 1) (k : ℕ) :
    P.map (fun ω (i : Fin k) => padInc r ξ u (i : ℕ) ω)
      = Measure.pi (fun _ : Fin k => gaussianReal 0 (Real.toNNReal (r ^ 2))) :=
  map_pi_of_stepIndep _ (measurable_padInc hξ hu)
    (map_padInc hξ hu hlaw hpast hunit)
    (indepFun_padInc_past hξ hu hlaw hpast hunit) k

end PaddingMap

/-! ## 5. `hincl` on the padded product space -/

omit [IsProbabilityMeasure P] in
/-- `padded_tail_of_increments`' `hincl` for an increment vector that reads only the chain: the
padding factor is a probability measure, so it integrates out. -/
theorem hincl_prod {N : ℕ} {δ : ℝ≥0} (Y : ℕ → Ω → ℝ) (hm : ∀ i, Measurable (Y i))
    (hpi : P.map (fun ω (i : Fin N) => Y (i : ℕ) ω)
      = Measure.pi fun _ : Fin N => gaussianReal 0 δ) :
    (P.prod (Measure.pi fun _ : Fin N => gaussianReal 0 δ)).map
        (fun q : Ω × (Fin N → ℝ) => fun i : Fin N => Y (i : ℕ) q.1)
      = Measure.pi fun _ : Fin N => gaussianReal 0 δ := by
  have hmv : Measurable (fun ω (i : Fin N) => Y (i : ℕ) ω) :=
    Measurable.of_eval (fun i => hm i)
  have hcomp : (fun q : Ω × (Fin N → ℝ) => fun i : Fin N => Y (i : ℕ) q.1)
      = (fun ω (i : Fin N) => Y (i : ℕ) ω) ∘ Prod.fst := rfl
  rw [hcomp, ← Measure.map_map hmv measurable_fst, Measure.map_fst_prod, measure_univ,
    one_smul, hpi]

/-! ## 6. The time-zero vanishing, and the per-step tail -/

omit [IsProbabilityMeasure P] in
/-- **Time zero.**  `padded_tail_of_increments`' own `hM₀ : 0 < M₀` says the point starts outside;
the contact set at step `0` is therefore empty, which is what report 40's Riemann comparison
needs. -/
theorem contact_zero_of_gap {n : ℕ} (C : ℕ → Ω → Finset (Fin n → ℤ))
    (W : Finset (Fin n → ℤ)) (M : (Fin n → ℤ) → ℕ → Ω → ℝ)
    (hhit : ∀ y ∈ W, {ω | y ∈ C 0 ω} ⊆ {ω | ∃ j ≤ 0, M y j ω ≤ 0})
    (hgap : ∀ y ∈ W, ∀ ω, 0 < M y 0 ω) :
    ∀ y ∈ W, P.real {ω | y ∈ C 0 ω} = 0 := by
  intro y hy
  have hempty : {ω | y ∈ C 0 ω} = (∅ : Set Ω) := by
    refine Set.eq_empty_of_subset_empty (le_trans (hhit y hy) ?_)
    intro ω hω
    obtain ⟨j, hj, hle⟩ := hω
    rw [Nat.le_zero.1 hj] at hle
    exact absurd hle (not_le.2 (hgap y hy ω))
  rw [hempty]
  simp [measureReal_def]

/-- **`tail_of_transport'`.**  `ChainRaw2.tail`, with the time-zero input replaced by the initial
gap.  The two remaining chain inputs are the containment `hhit` and the transported Proposition
4.1 `hprop`, which `TailTransport.hit_tail_yOf` supplies once `hincl_of_padding` and `hincl_prod`
have been fed to `Padding.padded_tail_of_increments`. -/
theorem tail_of_transport' {n : ℕ} {α : ℝ} (hn : 3 ≤ n) (hα : 0 < α)
    (C : ℕ → Ω → Finset (Fin n → ℤ)) (W : Finset (Fin n → ℤ))
    (M : (Fin n → ℤ) → ℕ → Ω → ℝ)
    (hwin : ∀ y ∈ W, ‖Tiling.toE n y‖ + Real.sqrt n / 2 ≤ windowC α n)
    (hr : ∀ y ∈ W, 0 < α * ‖Tiling.toE n y‖)
    (hy : ∀ k, k < ParamsAdopted2.numStepsAdopted2 n → k ≠ 0 → ∀ y ∈ W,
      0 < yOf (a0C n) ((k : ℝ) * ParamsAdopted2.stepSizeAdopted2 n)
        (α * ‖Tiling.toE n y‖))
    (hhit : ∀ k, k < ParamsAdopted2.numStepsAdopted2 n → ∀ y ∈ W,
      {ω | y ∈ C k ω} ⊆ {ω | ∃ j ≤ k, M y j ω ≤ 0})
    (hprop : ∀ k, k < ParamsAdopted2.numStepsAdopted2 n → k ≠ 0 → ∀ y ∈ W,
      P {ω | ∃ j ≤ k, M y j ω ≤ 0}
        ≤ ENNReal.ofReal (4 * Phi (yOf (a0C n)
            ((k : ℝ) * ParamsAdopted2.stepSizeAdopted2 n) (α * ‖Tiling.toE n y‖))))
    (hgap : ∀ y ∈ W, ∀ ω, 0 < M y 0 ω) :
    ∀ y ∈ W, ENNReal.ofReal (ContactIntegrated.intWeight P C
        (ParamsAdopted2.stepSizeAdopted2 n) (ParamsAdopted2.numStepsAdopted2 n) y)
      ≤ ENNReal.ofReal (4 * ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
          profileAt (a0C n) α (windowC α n) n t ‖Tiling.toE n y‖) :=
  tail_of_transport hn hα C W M hwin hr hy hhit hprop
    (contact_zero_of_gap C W M
      (fun y hy' => hhit 0 (by
        have h := ChainDrift.numSteps_pos (n := n) (e := 7) hn
        have h2 : 0 < ChainDrift.numSteps n 7 := by exact_mod_cast h
        exact h2) y hy') hgap)

end Submission.L10

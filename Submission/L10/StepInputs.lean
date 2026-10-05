import Submission.L10.Increments
import Submission.L10.GoodEvent

/-!
# Gate L-10 — H2 and H3 as theorems, and the good event on the `UT n` carrier

Report 12 left H2 (the centred increment) and H3 (the conditional second moment) as named
hypotheses because report 6 had not landed.  It has, so they are proved here from
`Submission.L10.Increments`:

* **H2** — `condExp_inner_starProjection` : `E[⟪c, π ξ⟫ | F] =ᵐ 0`;
* **H3** — `condExp_norm_sq_starProjection` : `E[‖π ξ‖² | F] =ᵐ dim (range π)`, and its scaled
  form `condExp_norm_sq_starProjection_smul` : `E[‖π (r • ξ)‖² | F] =ᵐ r² · dim`, which at
  `r = √h` is report 7 §8's `h · N_k`;
* **H1 with both discharged** — `driftInputs_step_gaussian`.

The second-moment identity `∫ ‖π x‖² dγ = dim (range π)` (`integral_norm_sq_starProjection`) is not
in Mathlib and is not in report 6; it is the analytic content of H3 and is proved here.

**Scope, stated precisely.**  `Increments.condExp_comp_of_indepFun` is for a **deterministic**
projection (report 6 §6 gap 3), so H2 and H3 below are for a deterministic `K` and a deterministic
`c`.  That is the "fixed `π_k` on each `F_k`-atom" form report 6 names as what the drift accounting
consumes.  The version with an `F`-measurable random `π` is still missing, and is still report 6's
gap 3 (80–100 lines); §6 of the accompanying report says so.

The good event is restated on report 6's carrier — `EuclideanSpace ℝ (UT n)`, because Mathlib has no
`MeasurableSpace` on `Matrix` at this pin — via `Increments.increment_opNorm_tail`.
-/

namespace Submission.L10.StepInputs

open MeasureTheory ProbabilityTheory Module Set Finset
open scoped ENNReal NNReal RealInnerProductSpace

/-! ## 1. Gaussian moments -/

section Moments

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- A continuous linear functional is square-integrable for a standard Gaussian. -/
theorem memLp_dual (L : StrongDual ℝ E) : MemLp (fun x => L x) 2 (stdGaussian E) := by
  have h1 : MemLp (fun x : E => ‖L‖ * ‖x‖) 2 (stdGaussian E) :=
    (IsGaussian.memLp_two_id.norm).const_mul ‖L‖
  refine MemLp.mono h1 (L.continuous.aestronglyMeasurable) ?_
  filter_upwards with x
  calc ‖L x‖ ≤ ‖L‖ * ‖x‖ := L.le_opNorm x
    _ = ‖‖L‖ * ‖x‖‖ := by rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]

/-- The second moment of a linear functional under a standard Gaussian is `‖L‖²`. -/
theorem integral_sq_dual (L : StrongDual ℝ E) :
    ∫ x, (L x) ^ 2 ∂(stdGaussian E) = ‖L‖ ^ 2 := by
  have hV := variance_dual_stdGaussian (E := E) L
  rw [variance_eq_sub (memLp_dual L)] at hV
  have h0 : (stdGaussian E)[fun x => L x] = 0 := integral_strongDual_stdGaussian L
  simp only [h0] at hV
  simpa using hV

/-- **The first moment of the projected step vanishes.**  This is the analytic content of H2. -/
theorem integral_inner_starProjection (K : Submodule ℝ E) [K.HasOrthogonalProjection] (c : E) :
    ∫ x, ⟪c, K.starProjection x⟫ ∂(stdGaussian E) = 0 := by
  have h := integral_strongDual_stdGaussian (E := E) ((innerSL ℝ c).comp K.starProjection)
  simpa using h

omit [MeasurableSpace E] [BorelSpace E] in
/-- `‖π x‖²` expanded in an orthonormal basis of the range, with the projection removed. -/
theorem norm_sq_starProjection_eq_sum (K : Submodule ℝ E) [K.HasOrthogonalProjection] (x : E) :
    ‖K.starProjection x‖ ^ 2 = ∑ i, ⟪x, ((stdOrthonormalBasis ℝ K) i : E)⟫ ^ 2 := by
  set b := stdOrthonormalBasis ℝ K
  have hmem := K.starProjection_apply_mem x
  have h1 := (b.sum_sq_inner_left (⟨K.starProjection x, hmem⟩ : K)).symm
  rw [show ‖(⟨K.starProjection x, hmem⟩ : K)‖ = ‖K.starProjection x‖ from rfl] at h1
  rw [h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  have hbi : ((b i : K) : E) ∈ K := (b i).2
  have hc : ⟪(⟨K.starProjection x, hmem⟩ : K), b i⟫ = ⟪K.starProjection x, ((b i : K) : E)⟫ := rfl
  rw [hc, K.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.mpr hbi]

/-- **The second moment of the projected step is the dimension of the range.**  This is the
analytic content of H3: `E ‖π ξ‖² = tr π = dim K`.  Not in Mathlib, and not in report 6. -/
theorem integral_norm_sq_starProjection (K : Submodule ℝ E) [K.HasOrthogonalProjection] :
    ∫ x, ‖K.starProjection x‖ ^ 2 ∂(stdGaussian E) = (Module.finrank ℝ K : ℝ) := by
  classical
  set b := stdOrthonormalBasis ℝ K with hb
  have hL : ∀ (i : Fin (Module.finrank ℝ K)) (x : E),
      ⟪x, ((b i : K) : E)⟫ = (innerSL ℝ ((b i : K) : E)) x := fun i x => real_inner_comm _ _
  have hnorm : ∀ i : Fin (Module.finrank ℝ K), ‖((b i : K) : E)‖ = 1 := by
    intro i
    rw [show ‖((b i : K) : E)‖ = ‖(b i : K)‖ from rfl]
    exact b.norm_eq_one i
  have hint : ∀ i : Fin (Module.finrank ℝ K),
      Integrable (fun x : E => ⟪x, ((b i : K) : E)⟫ ^ 2) (stdGaussian E) := by
    intro i
    refine ((memLp_dual (innerSL ℝ ((b i : K) : E))).integrable_sq).congr ?_
    filter_upwards with x
    rw [hL i x]
  have hsq : ∀ i : Fin (Module.finrank ℝ K),
      ∫ x, ⟪x, ((b i : K) : E)⟫ ^ 2 ∂(stdGaussian E) = 1 := by
    intro i
    have h1 : ∫ x, ⟪x, ((b i : K) : E)⟫ ^ 2 ∂(stdGaussian E)
        = ∫ x, ((innerSL ℝ ((b i : K) : E)) x) ^ 2 ∂(stdGaussian E) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show ⟪x, ((b i : K) : E)⟫ ^ 2 = _
      rw [hL i x]
    rw [h1, integral_sq_dual, innerSL_apply_norm, hnorm i, one_pow]
  calc ∫ x, ‖K.starProjection x‖ ^ 2 ∂(stdGaussian E)
      = ∫ x, ∑ i, ⟪x, ((b i : K) : E)⟫ ^ 2 ∂(stdGaussian E) :=
        integral_congr_ae (Filter.Eventually.of_forall (norm_sq_starProjection_eq_sum K))
    _ = ∑ i, ∫ x, ⟪x, ((b i : K) : E)⟫ ^ 2 ∂(stdGaussian E) :=
        integral_finsetSum _ (fun i _ => hint i)
    _ = (Module.finrank ℝ K : ℝ) := by
        rw [Finset.sum_congr rfl fun i _ => hsq i]
        simp

end Moments

/-! ## 2. H2 and H3 as conditional expectations -/

section Conditional

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {α : Type*} [mα : MeasurableSpace α]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [mE : MeasurableSpace E] [BorelSpace E]

/-- **H2.**  The middle term of the one-step expansion has conditional mean zero. -/
theorem condExp_inner_starProjection {Z : Ω → α} (hZ : Measurable Z) {ξ : Ω → E}
    (hξ : Measurable ξ) (hind : IndepFun ξ Z P) (hlaw : P.map ξ = stdGaussian E)
    (K : Submodule ℝ E) [K.HasOrthogonalProjection] (c : E) :
    P[fun ω => ⟪c, K.starProjection (ξ ω)⟫|MeasurableSpace.comap Z mα] =ᵐ[P] 0 := by
  have h := Increments.condExp_comp_of_indepFun hZ hξ hind
    (f := fun y : E => ⟪c, y⟫) ((innerSL ℝ c).continuous.measurable)
    (π := K.starProjection) (K.starProjection.continuous.measurable)
  refine h.trans (Filter.Eventually.of_forall fun ω => ?_)
  rw [hlaw, integral_inner_starProjection K c]
  rfl

/-- **H3.**  The conditional second moment of the projected step is the dimension of the free
subspace — Klartag's `N_t = dim F_t` (eq. 39, p. 13). -/
theorem condExp_norm_sq_starProjection {Z : Ω → α} (hZ : Measurable Z) {ξ : Ω → E}
    (hξ : Measurable ξ) (hind : IndepFun ξ Z P) (hlaw : P.map ξ = stdGaussian E)
    (K : Submodule ℝ E) [K.HasOrthogonalProjection] :
    P[fun ω => ‖K.starProjection (ξ ω)‖ ^ 2|MeasurableSpace.comap Z mα]
      =ᵐ[P] fun _ => (Module.finrank ℝ K : ℝ) := by
  have h := Increments.condExp_comp_of_indepFun hZ hξ hind
    (f := fun y : E => ‖y‖ ^ 2) ((measurable_norm).pow_const 2)
    (π := K.starProjection) (K.starProjection.continuous.measurable)
  refine h.trans (Filter.Eventually.of_forall fun ω => ?_)
  rw [hlaw, integral_norm_sq_starProjection K]

/-- **H3 at the chain's scale.**  The increment at step size `h` is `√h • ξ` with `ξ` standard, so
the conditional second moment is `h · N_k`. -/
theorem condExp_norm_sq_starProjection_smul {Z : Ω → α} (hZ : Measurable Z) {ξ : Ω → E}
    (hξ : Measurable ξ) (hind : IndepFun ξ Z P) (hlaw : P.map ξ = stdGaussian E)
    (K : Submodule ℝ E) [K.HasOrthogonalProjection] (r : ℝ) :
    P[fun ω => ‖K.starProjection (r • ξ ω)‖ ^ 2|MeasurableSpace.comap Z mα]
      =ᵐ[P] fun _ => r ^ 2 * (Module.finrank ℝ K : ℝ) := by
  have hfun : (fun ω => ‖K.starProjection (r • ξ ω)‖ ^ 2)
      = (r ^ 2 : ℝ) • (fun ω => ‖K.starProjection (ξ ω)‖ ^ 2) := by
    funext ω
    show ‖K.starProjection (r • ξ ω)‖ ^ 2 = r ^ 2 * ‖K.starProjection (ξ ω)‖ ^ 2
    rw [map_smul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [hfun]
  refine (condExp_smul (r ^ 2 : ℝ) _ _).trans ?_
  filter_upwards [condExp_norm_sq_starProjection hZ hξ hind hlaw K] with ω hbase
  simp only [Pi.smul_apply, smul_eq_mul, hbase]

end Conditional

/-! ## 3. The good event on report 6's carrier -/

section Good

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ}

/-- The good event on the carrier report 6 uses (`EuclideanSpace ℝ (UT n)`, because Mathlib has no
`MeasurableSpace` on `Matrix` at this pin).  `r • symMat ξ` is the symmetric matrix of the
increment; `Increments.measurable_opNorm_mkMat` makes the event measurable. -/
def goodEventUT (r : ℝ) (ξ : Ω → EuclideanSpace ℝ (Increments.UT n)) (thr : ℝ) : Set Ω :=
  {ω | ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (r • Increments.symMat (ξ ω))‖ ≤ thr}

/-- **`μ(Sᶜ) ≤ 4 exp(−s²n)` on the `UT n` carrier**, from `Increments.increment_opNorm_tail`.
This is report 12's good event moved onto the carrier the chain actually lives on. -/
theorem measureReal_compl_goodEventUT_le {r : ℝ} (hr : 0 < r)
    {ξ : Ω → EuclideanSpace ℝ (Increments.UT n)} (hξ : Measurable ξ)
    (hlaw : P.map ξ = stdGaussian (EuclideanSpace ℝ (Increments.UT n)))
    (s : ℝ) (hs : 1 ≤ s) :
    P.real (goodEventUT r ξ (6 * r * s * Real.sqrt n))ᶜ ≤ 4 * Real.exp (-(s ^ 2 * n)) := by
  refine le_trans (measureReal_mono ?_ (measure_ne_top P _))
    (Increments.increment_opNorm_tail hr hξ hlaw s hs)
  intro ω hω
  have hω' : ¬ (‖Matrix.toEuclideanCLM (𝕜 := ℝ) (r • Increments.symMat (ξ ω))‖
      ≤ 6 * r * s * Real.sqrt n) := hω
  exact le_of_lt (not_le.mp hω')

end Good

/-! ## 4. H1 with H2 and H3 discharged -/

section H1

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {α : Type*} [mα : MeasurableSpace α]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [mE : MeasurableSpace E] [BorelSpace E]

/-- **H1 with H2 and H3 proved rather than assumed.**  The only remaining input is the pointwise
one-step bound, which is `GoodEvent.log_det_step_le` transported along the matrix model; the two
conditional laws are discharged by `condExp_inner_starProjection` and
`condExp_norm_sq_starProjection_smul`.

`κ = r² / (2 (1+δ)² ‖A‖²_op)` at the wiring, matching report 7 §5.2's
`κ = h / (2 ‖A‖²_op κ²)` with `r = √h`. -/
theorem condExp_step_le_gaussian {Z : Ω → α} (hZ : Measurable Z) {ξ : Ω → E}
    (hξ : Measurable ξ) (hind : IndepFun ξ Z P) (hlaw : P.map ξ = stdGaussian E)
    (K : Submodule ℝ E) [K.HasOrthogonalProjection] (c : E) (r lam : ℝ)
    [SigmaFinite (P.trim (Measurable.comap_le hZ))]
    {Dk Dk1 errk : Ω → ℝ}
    (hpt : ∀ᵐ ω ∂P, Dk1 ω ≤ Dk ω + ⟪c, K.starProjection (ξ ω)⟫
      - lam * ‖K.starProjection (r • ξ ω)‖ ^ 2 + errk ω)
    (hDkm : StronglyMeasurable[MeasurableSpace.comap Z mα] Dk)
    (herrm : StronglyMeasurable[MeasurableSpace.comap Z mα] errk)
    (iDk1 : Integrable Dk1 P) (iDk : Integrable Dk P)
    (itr : Integrable (fun ω => ⟪c, K.starProjection (ξ ω)⟫) P)
    (iquad : Integrable (fun ω => lam * ‖K.starProjection (r • ξ ω)‖ ^ 2) P)
    (ierr : Integrable errk P) :
    P[Dk1|MeasurableSpace.comap Z mα] ≤ᵐ[P]
      fun ω => Dk ω - lam * r ^ 2 * (Module.finrank ℝ K : ℝ) + errk ω := by
  have h2 : P[fun ω => ⟪c, K.starProjection (ξ ω)⟫|MeasurableSpace.comap Z mα] =ᵐ[P] 0 :=
    condExp_inner_starProjection hZ hξ hind hlaw K c
  have hfun : (fun ω => lam * ‖K.starProjection (r • ξ ω)‖ ^ 2)
      = (lam : ℝ) • (fun ω => ‖K.starProjection (r • ξ ω)‖ ^ 2) := rfl
  have h3 : P[fun ω => lam * ‖K.starProjection (r • ξ ω)‖ ^ 2|MeasurableSpace.comap Z mα]
      =ᵐ[P] fun ω => (lam * r ^ 2) * (Module.finrank ℝ K : ℝ) := by
    rw [hfun]
    refine (condExp_smul (lam : ℝ) _ _).trans ?_
    filter_upwards [condExp_norm_sq_starProjection_smul hZ hξ hind hlaw K r] with ω hbase
    simp only [Pi.smul_apply, smul_eq_mul, hbase]
    ring
  have hstep := GoodEvent.condExp_step_le (μ := P) (Measurable.comap_le hZ) hpt hDkm herrm
    iDk1 iDk itr iquad ierr h2
    (Nk := fun _ => (Module.finrank ℝ K : ℝ)) (κ := lam * r ^ 2) h3
  exact hstep

end H1

end Submission.L10.StepInputs

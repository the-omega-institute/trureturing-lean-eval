import Submission.L10.StepInputs
import Submission.L10.StepInputs2

/-!
# Gate L-10 (`klartag_packing`), brief 15 — reconciling the two step-input modules

`Submission/L10/StepInputs.lean` (brief 12's addendum, report 12b) proves H2 and H3 for a
**deterministic** projection `K` and a deterministic `c`, and restates the accumulated good event on
the `UT n` carrier (`goodEventUT`).  `Submission/L10/StepInputs2.lean` (brief 15, report 15) proves
the **random `ℱ`-measurable** versions — which is what `ChainDrift.DriftInputs.step` needs, since the
chain's `N_k = Chain.freeDim …` is not constant — together with the per-step bound and the
Frobenius-to-operator bridge.

Both files are reported and frozen, so the reconciliation lives here (rule 5).  Two jobs:

1. **Currency.**  `StepInputs2`'s H2/H3 take the increment's law as *coordinate* hypotheses
   (`iIndepFun` of the coordinates, and each coordinate `N(0, v)`), while the rest of the tree —
   `StepInputs`, `Increments.increment_opNorm_tail`, `GoodEvent` — states it as
   `P.map ξ = stdGaussian (EuclideanSpace ℝ ι)`.  `coord_law`, `coord_indep` and their scaled forms
   convert, so a caller holding the law hypothesis can use the random-`π` theorems.
2. **The good event.**  `chainGood` is the intersection of `StepInputs.goodEventUT` (the accumulated
   Gaussian part, report 12 §1) with `StepInputs2.stepGood` (the `N` single steps, report 15 §2),
   and `measureReal_compl_chainGood_le` adds the two failure probabilities.  That is the event
   `GoodEvent.oneStep_of_good` consumes at every step.
-/

namespace Submission.L10.StepGlue

open MeasureTheory ProbabilityTheory Matrix Finset Module
open scoped ENNReal NNReal RealInnerProductSpace
open Submission.L10.Increments Submission.L10.StepInputs2

set_option linter.unusedSectionVars false

noncomputable section

/-! ## 1. From the law of the increment to the coordinate hypotheses -/

section Currency

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {ι : Type*} [Fintype ι]

/-- Each coordinate of a standard Gaussian on `EuclideanSpace ℝ ι` is `N(0,1)`. -/
theorem stdGaussian_coord_law (p : ι) :
    (stdGaussian (EuclideanSpace ℝ ι)).map (fun x => x p) = gaussianReal 0 1 := by
  rw [← map_pi_eq_stdGaussian (ι := ι), Measure.map_map (by fun_prop) (by fun_prop),
    show ((fun x : EuclideanSpace ℝ ι => x p) ∘ (WithLp.toLp 2))
      = fun (x : ι → ℝ) => x p from rfl]
  exact (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) p).map_eq

/-- A random variable with the standard Gaussian law has `N(0,1)` coordinates. -/
theorem coord_law {ξ : Ω → EuclideanSpace ℝ ι} (hξ : Measurable ξ)
    (hlaw : P.map ξ = stdGaussian (EuclideanSpace ℝ ι)) (p : ι) :
    P.map (fun ω => ξ ω p) = gaussianReal 0 1 := by
  rw [show (fun ω => ξ ω p) = (fun x : EuclideanSpace ℝ ι => x p) ∘ ξ from rfl,
    ← Measure.map_map (by fun_prop) hξ, hlaw, stdGaussian_coord_law]

/-- …and independent coordinates. -/
theorem coord_indep {ξ : Ω → EuclideanSpace ℝ ι} (hξ : Measurable ξ)
    (hlaw : P.map ξ = stdGaussian (EuclideanSpace ℝ ι)) :
    iIndepFun (fun (p : ι) (ω : Ω) => ξ ω p) P := by
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun p => (Measurable.aemeasurable (by fun_prop)))]
  have hofLp : (stdGaussian (EuclideanSpace ℝ ι)).map WithLp.ofLp
      = Measure.pi (fun _ : ι => gaussianReal 0 1) := by
    rw [← map_pi_eq_stdGaussian (ι := ι), Measure.map_map (by fun_prop) (by fun_prop),
      show (WithLp.ofLp ∘ (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι)) = id from rfl,
      Measure.map_id]
  have h1 : P.map (fun ω p => ξ ω p) = Measure.pi (fun _ : ι => gaussianReal 0 1) := by
    rw [show (fun (ω : Ω) (p : ι) => ξ ω p) = WithLp.ofLp ∘ ξ from rfl,
      ← Measure.map_map (by fun_prop) hξ, hlaw, hofLp]
  rw [h1]
  congr 1
  funext p
  rw [coord_law hξ hlaw]

/-- The chain's increment is `r • ξ` with `ξ` standard, so its coordinates are `N(0, r²)`. -/
theorem coord_law_smul {ξ : Ω → EuclideanSpace ℝ ι} (hξ : Measurable ξ)
    (hlaw : P.map ξ = stdGaussian (EuclideanSpace ℝ ι)) (r : ℝ) (p : ι) :
    P.map (fun ω => (r • ξ ω) p) = gaussianReal 0 (Real.toNNReal (r ^ 2)) := by
  have hfun : (fun ω => (r • ξ ω) p) = (fun t : ℝ => r * t) ∘ (fun ω => ξ ω p) := rfl
  rw [hfun, ← Measure.map_map (by fun_prop) (by fun_prop), coord_law hξ hlaw,
    show (fun t : ℝ => r * t) = (r * ·) from rfl, gaussianReal_map_const_mul]
  refine gaussianReal_ext_iff.2 ⟨by ring, ?_⟩
  refine NNReal.coe_injective ?_
  rw [NNReal.coe_mul, Real.coe_toNNReal _ (sq_nonneg r)]
  simp

/-- …and they stay independent. -/
theorem coord_indep_smul {ξ : Ω → EuclideanSpace ℝ ι} (hξ : Measurable ξ)
    (hlaw : P.map ξ = stdGaussian (EuclideanSpace ℝ ι)) (r : ℝ) :
    iIndepFun (fun (p : ι) (ω : Ω) => (r • ξ ω) p) P :=
  (coord_indep hξ hlaw).comp (fun _ => fun t : ℝ => r * t) (fun _ => by fun_prop)

end Currency

/-! ## 2. H3 for the chain's increment, with a random projection -/

section H3Chain

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Report 7 §8's H3 at the chain's scale, for a random `ℱ`-measurable free subspace.**
`E[‖π_k (√h · ξ_k)‖² | ℱ_k] = h · N_k` with `N_k = dim (K ω)`.  `StepInputs.condExp_norm_sq_
starProjection_smul` is the same statement for a *fixed* `K`; here `K` varies with `ω`, which is
what `ChainDrift.DriftInputs.step` needs. -/
theorem condExp_norm_sq_starProjection_smul_random
    {K : Ω → Submodule ℝ (EuclideanSpace ℝ ι)} {ξ : Ω → EuclideanSpace ℝ ι} (r : ℝ)
    (hξm : Measurable ξ) (hlaw : P.map ξ = stdGaussian (EuclideanSpace ℝ ι))
    (hintprod : ∀ p q : ι, Integrable (fun ω => (r • ξ ω) p * (r • ξ ω) q) P)
    (hint : ∀ p q : ι, Integrable (fun ω =>
      ((K ω).starProjection (EuclideanSpace.single p (1:ℝ))) q
        * ((r • ξ ω) p * (r • ξ ω) q)) P)
    {ℱ : MeasurableSpace Ω} (hℱ : ℱ ≤ mΩ) [SigmaFinite (P.trim hℱ)]
    (hM : ∀ p q : ι, StronglyMeasurable[ℱ]
      fun ω => ((K ω).starProjection (EuclideanSpace.single p (1:ℝ))) q)
    (hind : Indep (MeasurableSpace.comap (fun ω => r • ξ ω) inferInstance) ℱ P) :
    P[fun ω => ‖(K ω).starProjection (r • ξ ω)‖ ^ 2 | ℱ]
      =ᵐ[P] fun ω => r ^ 2 * (finrank ℝ (K ω) : ℝ) := by
  have hrm : Measurable[mΩ] fun ω => r • ξ ω := hξm.const_smul r
  have h := condExp_norm_starProjection_sq (mΩ := mΩ) (K := K) (ξ := fun ω => r • ξ ω)
    (v := Real.toNNReal (r ^ 2)) hrm (coord_indep_smul (mΩ := mΩ) hξm hlaw r)
    (coord_law_smul (mΩ := mΩ) hξm hlaw r) hintprod hint hℱ hM hind
  refine h.trans (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.coe_toNNReal _ (sq_nonneg r)]

end H3Chain

/-! ## 3. The good event the wiring consumes: accumulated ∩ per-step -/

section GoodEvent

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ}

/-- The full good event: report 12's accumulated operator-norm bound **and** report 15's per-step
bound at every one of the `N` steps. -/
def chainGood (r : ℝ) (W : Ω → EuclideanSpace ℝ (UT n))
    (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (thr : ℝ) (N : ℕ) (η : ℝ) : Set Ω :=
  Submission.L10.StepInputs.goodEventUT r W thr ∩ stepGood ξ N η

/-- **The failure probability of the full good event**, the two costs added. -/
theorem measureReal_compl_chainGood_le {r : ℝ} (hr : 0 < r)
    {W : Ω → EuclideanSpace ℝ (UT n)} (hW : Measurable W)
    (hWlaw : P.map W = stdGaussian (EuclideanSpace ℝ (UT n)))
    {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)} {v : ℝ≥0}
    (hlaw : ∀ k, ∀ p : UT n, P.map (fun ω => ξ k ω p) = gaussianReal 0 v)
    {η : ℝ} (hη : 0 < η) (N : ℕ) (s : ℝ) (hs : 1 ≤ s) :
    P.real (chainGood r W ξ (6 * r * s * Real.sqrt n) N η)ᶜ
      ≤ 4 * Real.exp (-(s ^ 2 * n))
        + (N : ℝ) * ((Fintype.card (UT n) : ℝ)
            * (2 * Real.exp (-(η ^ 2 / (Fintype.card (UT n) : ℝ)) / (2 * v)))) := by
  have hcompl : (chainGood r W ξ (6 * r * s * Real.sqrt n) N η)ᶜ
      = (Submission.L10.StepInputs.goodEventUT r W (6 * r * s * Real.sqrt n))ᶜ
        ∪ (stepGood ξ N η)ᶜ := by
    rw [chainGood, Set.compl_inter]
  rw [hcompl]
  refine (measureReal_union_le _ _).trans ?_
  exact add_le_add
    (Submission.L10.StepInputs.measureReal_compl_goodEventUT_le hr hW hWlaw s hs)
    (measureReal_compl_stepGood_le hlaw hη N)

end GoodEvent

end

end Submission.L10.StepGlue

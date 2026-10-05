import Submission.L10.Theorem
import Submission.L10.WalkTelescope

/-!
# Gate L-10 (`klartag_packing`), brief 47 — the probability space the chain runs on

Report 46 named Residual B: every module in the tree carries the driving sequence `ξ` abstractly,
with `P.map (ξ k) = stdGaussian`, independence of the past, integrability and a filtration as
hypotheses, and **no brief had been asked to build the space**.  This module builds it.

## The space

`Ω := ℕ → E` with `P := Measure.infinitePi (fun _ : ℕ => stdGaussian E)`.  **The pin does have a
countable (indeed arbitrary) product of probability measures** — `MeasureTheory.Measure.infinitePi`
(`Mathlib/Probability/ProductMeasure.lean`), with `infinitePi_map_eval`,
`measurePreserving_eval_infinitePi` and `iIndepFun_iff_map_fun_eq_infinitePi_map` — so the brief's
fallback shape `(Fin N → E) × Ω'` is not needed and is worse: a `Fin N` product cannot satisfy
`Theorem.ChainSetup`'s `∀ k` law, and an extra factor `Ω'` buys nothing that changing the *value*
type does not.  Everything below is stated for a general value type `F`, so the padding's fresh
coordinates are obtained by taking `F := WithLp 2 (E × ℝ)` and post-composing with the two
projections — no second factor, and the one `iIndepFun_coord` still carries all the independence.

## What is here

1. `gaussPath F`, `coord k`, `map_coord`, `iIndepFun_coord` — the space and the coordinates.
2. `natFil`, `filtration`, `measurable_coord_natFil`, `indep_coord_natFil` — the natural filtration,
   as a bundled `MeasureTheory.Filtration`, with each `ξ k` measurable for `ℱ (k+1)` and independent
   of `ℱ k`; and the `SigmaFinite (P.trim ·)` instance the conditional expectations need.
3. `memLp_coord_apply` and the `Integrable` corollaries — every moment hypothesis about `ξ` that
   `StepInputs2.driftInputs_step_chain` takes, from `memLp_id_gaussianReal`.
4. `chainSetup : Theorem.ChainSetup n` — the record, fully constructed, for every `n`.

## What is *not* here, and why

`driftInputs_step_chain`'s remaining four integrability hypotheses — `hintV`, `hinttr`, `hintD`,
`hinterr` — are **not** Gaussian moments: `V k = π_k (A_k⁻¹)`, `D k = log det A_k` and
`err k = chainErr k` are unbounded off the good event, where `A_k` may be singular.  They need a
bound on the chain's own data, not on `ξ`.  See the report, §4.
-/

set_option warn.classDefReducibility false

namespace Submission.L10.ChainSetup

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal RealInnerProductSpace
open Submission.L10 Submission.L10.Increments

noncomputable section

/-! ## 1. The space and its coordinates -/

section Space

variable (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- **The path space**: one standard Gaussian per step, for infinitely many steps. -/
def gaussPath : Measure (ℕ → F) := Measure.infinitePi fun _ : ℕ => stdGaussian F

instance isProbabilityMeasure_gaussPath : IsProbabilityMeasure (gaussPath F) := by
  rw [gaussPath]; infer_instance

variable {F}

/-- **The `k`-th driving increment.** -/
def coord (k : ℕ) : (ℕ → F) → F := fun ω => ω k

omit [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [BorelSpace F] in
theorem measurable_coord (k : ℕ) : Measurable (coord (F := F) k) := measurable_pi_apply k

omit [BorelSpace F] in
/-- **The law of each coordinate is the standard Gaussian.** -/
theorem map_coord (k : ℕ) : (gaussPath F).map (coord k) = stdGaussian F :=
  Measure.infinitePi_map_eval (fun _ : ℕ => stdGaussian F) k

omit [BorelSpace F] in
/-- **The coordinates are independent.** -/
theorem iIndepFun_coord : iIndepFun (coord (F := F)) (gaussPath F) := by
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (fun k => measurable_coord k)]
  have h1 : (fun (ω : ℕ → F) (k : ℕ) => coord k ω) = fun ω => ω := rfl
  rw [h1, Measure.map_id']
  have h2 : (fun k : ℕ => (gaussPath F).map (coord k)) = fun _ : ℕ => stdGaussian F := by
    funext k; exact map_coord k
  rw [h2]
  rfl

end Space

/-! ## 2. The natural filtration -/

section Filtration

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- The first `k` increments. -/
def restr (k : ℕ) : (ℕ → F) → (Fin k → F) := fun ω j => ω j

omit [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [BorelSpace F] in
theorem measurable_restr (k : ℕ) : Measurable (restr (F := F) k) :=
  Measurable.of_eval fun _j => measurable_pi_apply _

/-- **The natural filtration of the driving sequence.** -/
def natFil (k : ℕ) : MeasurableSpace (ℕ → F) :=
  MeasurableSpace.comap (restr (F := F) k) inferInstance

omit [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [BorelSpace F] in
theorem natFil_le (k : ℕ) : natFil (F := F) k ≤ (inferInstance : MeasurableSpace (ℕ → F)) :=
  (measurable_restr k).comap_le

omit [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [BorelSpace F] in
theorem monotone_natFil : Monotone (natFil (F := F)) := by
  intro k m hkm s hs
  obtain ⟨t, ht, rfl⟩ := hs
  exact ⟨(fun u : Fin m → F => fun j : Fin k => u ⟨j, lt_of_lt_of_le j.isLt hkm⟩) ⁻¹' t,
    (Measurable.of_eval fun _j => measurable_pi_apply _) ht, rfl⟩

/-- **The filtration, bundled.** -/
def filtration : Filtration ℕ (inferInstance : MeasurableSpace (ℕ → F)) where
  seq := natFil
  mono' := monotone_natFil
  le' := natFil_le

instance sigmaFinite_trim_natFil (k : ℕ) :
    SigmaFinite ((gaussPath F).trim (natFil_le (F := F) k)) := by
  have : IsFiniteMeasure ((gaussPath F).trim (natFil_le (F := F) k)) := inferInstance
  infer_instance

omit [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [BorelSpace F] in
/-- **`ξ k` is `ℱ (k+1)`-measurable** — the sequence is adapted. -/
theorem measurable_coord_natFil (k : ℕ) : Measurable[natFil (F := F) (k + 1)] (coord k) := by
  have h : coord (F := F) k
      = (fun u : Fin (k + 1) → F => u ⟨k, Nat.lt_succ_self k⟩) ∘ restr (k + 1) := rfl
  rw [h]
  exact (measurable_pi_apply _).comp (Measurable.of_comap_le le_rfl)

omit [BorelSpace F] in
/-- **`ξ k` is independent of the first `k` increments.** -/
theorem indepFun_coord_restr (k : ℕ) :
    IndepFun (coord (F := F) k) (restr k) (gaussPath F) := by
  classical
  have hdisj : Disjoint ({k} : Finset ℕ) (Finset.range k) := by
    simp [Finset.disjoint_singleton_left]
  have hbase := (iIndepFun_coord (F := F)).indepFun_finset {k} (Finset.range k) hdisj
    (fun j => measurable_coord j)
  have hf : Measurable fun u : (↥({k} : Finset ℕ) → F) => u ⟨k, Finset.mem_singleton_self k⟩ :=
    measurable_pi_apply _
  have hg : Measurable fun u : (↥(Finset.range k) → F) =>
      (fun j : Fin k => u ⟨j, Finset.mem_range.2 j.isLt⟩) :=
    Measurable.of_eval fun _j => measurable_pi_apply _
  have hcomp := hbase.comp hf hg
  have e1 : ((fun u : (↥({k} : Finset ℕ) → F) => u ⟨k, Finset.mem_singleton_self k⟩)
      ∘ fun (ω : ℕ → F) (j : ↥({k} : Finset ℕ)) => coord (j : ℕ) ω) = coord k := rfl
  have e2 : ((fun u : (↥(Finset.range k) → F) =>
        (fun j : Fin k => u ⟨j, Finset.mem_range.2 j.isLt⟩))
      ∘ fun (ω : ℕ → F) (j : ↥(Finset.range k)) => coord (j : ℕ) ω) = restr k := rfl
  rwa [e1, e2] at hcomp

omit [BorelSpace F] in
/-- …in the `Indep`-of-σ-algebras shape `StepInputs2.driftInputs_step_chain` takes. -/
theorem indep_coord_natFil (k : ℕ) :
    Indep (MeasurableSpace.comap (coord (F := F) k) inferInstance) (natFil k) (gaussPath F) :=
  indepFun_coord_restr k

end Filtration

/-! ## 3. Moments -/

section Moments

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem coord_law (k : ℕ) (p : ι) :
    (gaussPath (EuclideanSpace ℝ ι)).map (fun ω : ℕ → EuclideanSpace ℝ ι => coord k ω p)
      = gaussianReal 0 1 :=
  StepGlue.coord_law (measurable_coord k) (map_coord k) p

omit [DecidableEq ι] in
theorem coord_indep (k : ℕ) :
    iIndepFun (fun (p : ι) (ω : ℕ → EuclideanSpace ℝ ι) => coord k ω p)
      (gaussPath (EuclideanSpace ℝ ι)) :=
  StepGlue.coord_indep (measurable_coord k) (map_coord k)

/-- **All moments of every coordinate are finite**, from `memLp_id_gaussianReal`. -/
theorem memLp_coord_apply (k : ℕ) (p : ι) (r : ℝ≥0∞) (hr : r ≠ ∞) :
    MemLp (fun ω : ℕ → EuclideanSpace ℝ ι => coord k ω p) r (gaussPath (EuclideanSpace ℝ ι)) := by
  have hm : Measurable fun ω : ℕ → EuclideanSpace ℝ ι => coord k ω p :=
    StepInputs2.measurable_coord (measurable_coord k) p
  have h : MemLp id r ((gaussPath (EuclideanSpace ℝ ι)).map
      (fun ω : ℕ → EuclideanSpace ℝ ι => coord k ω p)) := by
    rw [coord_law k p]; exact memLp_id_gaussianReal' r hr
  exact (memLp_map_measure_iff aestronglyMeasurable_id hm.aemeasurable).1 h

theorem integrable_coord_apply (k : ℕ) (p : ι) :
    Integrable (fun ω : ℕ → EuclideanSpace ℝ ι => coord k ω p)
      (gaussPath (EuclideanSpace ℝ ι)) :=
  memLp_one_iff_integrable.1 (memLp_coord_apply k p 1 (by simp))

theorem integrable_coord_mul (k : ℕ) (p q : ι) :
    Integrable (fun ω : ℕ → EuclideanSpace ℝ ι => coord k ω p * coord k ω q)
      (gaussPath (EuclideanSpace ℝ ι)) := by
  have hH : ENNReal.HolderTriple 2 2 1 := ⟨by rw [ENNReal.inv_two_add_inv_two]; simp⟩
  exact MemLp.integrable_mul (memLp_coord_apply k p 2 (by simp))
    (memLp_coord_apply k q 2 (by simp))

/-- `‖ξ_k‖²` is integrable — the second moment that dominates `hintquad`, since
`‖π x‖ ≤ ‖x‖`. -/
theorem integrable_norm_sq_coord (k : ℕ) :
    Integrable (fun ω : ℕ → EuclideanSpace ℝ ι => ‖coord k ω‖ ^ 2)
      (gaussPath (EuclideanSpace ℝ ι)) := by
  have hsum : ∀ ω : ℕ → EuclideanSpace ℝ ι,
      ‖coord k ω‖ ^ 2 = ∑ p : ι, coord k ω p * coord k ω p := by
    intro ω
    rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
    simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
  simp only [hsum]
  exact integrable_finsetSum _ fun p _ => integrable_coord_mul k p p

end Moments

/-! ## 4. The chain's increments at scale `c = √h`, and `driftInputs_step_chain` on the path -/

section Step

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The chain's increment**: the standard coordinate scaled by `c = √h`. -/
def step (c : ℝ) (k : ℕ) (ω : ℕ → EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι := c • coord k ω

omit [DecidableEq ι] in
theorem measurable_step (c : ℝ) (k : ℕ) : Measurable (step (ι := ι) c k) :=
  (measurable_coord k).const_smul c

omit [Fintype ι] [DecidableEq ι] in
theorem step_apply (c : ℝ) (k : ℕ) (ω : ℕ → EuclideanSpace ℝ ι) (p : ι) :
    step c k ω p = c * coord k ω p := rfl

omit [DecidableEq ι] in
/-- `ξ_k ~ N(0, c²·Id)` — the currency `StateInvariant4`'s half-laws take. -/
theorem map_step (c : ℝ) (k : ℕ) :
    (gaussPath (EuclideanSpace ℝ ι)).map (step c k)
      = StateInvariant.scaled c (EuclideanSpace ℝ ι) := by
  rw [show (step (ι := ι) c k) = (fun x : EuclideanSpace ℝ ι => c • x) ∘ coord k from rfl,
    ← Measure.map_map (by fun_prop) (measurable_coord k), map_coord k]
  rfl

omit [DecidableEq ι] in
theorem iIndepFun_step (c : ℝ) :
    iIndepFun (step (ι := ι) c) (gaussPath (EuclideanSpace ℝ ι)) :=
  (iIndepFun_coord (F := EuclideanSpace ℝ ι)).comp
    (fun _ : ℕ => fun x : EuclideanSpace ℝ ι => c • x) (fun _ => measurable_id.const_smul c)

omit [DecidableEq ι] in
/-- `hlaw` of `driftInputs_step_chain`, at `v = c²`. -/
theorem step_coord_law (c : ℝ) (k : ℕ) (p : ι) :
    (gaussPath (EuclideanSpace ℝ ι)).map (fun ω : ℕ → EuclideanSpace ℝ ι => step c k ω p)
      = gaussianReal 0 (Real.toNNReal (c ^ 2)) :=
  StepGlue.coord_law_smul (measurable_coord k) (map_coord k) c p

omit [DecidableEq ι] in
/-- `hindep` of `driftInputs_step_chain`. -/
theorem step_coord_indep (c : ℝ) (k : ℕ) :
    iIndepFun (fun (p : ι) (ω : ℕ → EuclideanSpace ℝ ι) => step c k ω p)
      (gaussPath (EuclideanSpace ℝ ι)) :=
  StepGlue.coord_indep_smul (measurable_coord k) (map_coord k) c

omit [DecidableEq ι] in
/-- `hind` of `driftInputs_step_chain`: each increment is independent of its own past. -/
theorem indep_step_natFil (c : ℝ) (k : ℕ) :
    Indep (MeasurableSpace.comap (step (ι := ι) c k) inferInstance) (natFil k)
      (gaussPath (EuclideanSpace ℝ ι)) :=
  (indepFun_coord_restr (F := EuclideanSpace ℝ ι) k).comp
    (measurable_id.const_smul c) measurable_id

theorem memLp_step_apply (c : ℝ) (k : ℕ) (p : ι) (r : ℝ≥0∞) (hr : r ≠ ∞) :
    MemLp (fun ω : ℕ → EuclideanSpace ℝ ι => step c k ω p) r
      (gaussPath (EuclideanSpace ℝ ι)) := by
  have he : (fun ω : ℕ → EuclideanSpace ℝ ι => step c k ω p)
      = fun ω : ℕ → EuclideanSpace ℝ ι => c * coord k ω p := rfl
  rw [he]
  exact (memLp_coord_apply k p r hr).const_mul c

/-- `hintxi` of `driftInputs_step_chain`. -/
theorem integrable_step_apply (c : ℝ) (k : ℕ) (p : ι) :
    Integrable (fun ω : ℕ → EuclideanSpace ℝ ι => step c k ω p)
      (gaussPath (EuclideanSpace ℝ ι)) :=
  memLp_one_iff_integrable.1 (memLp_step_apply c k p 1 (by simp))

/-- `hintprod` of `driftInputs_step_chain`. -/
theorem integrable_step_mul (c : ℝ) (k : ℕ) (p q : ι) :
    Integrable (fun ω : ℕ → EuclideanSpace ℝ ι => step c k ω p * step c k ω q)
      (gaussPath (EuclideanSpace ℝ ι)) := by
  have hH : ENNReal.HolderTriple 2 2 1 := ⟨by rw [ENNReal.inv_two_add_inv_two]; simp⟩
  exact MemLp.integrable_mul (memLp_step_apply c k p 2 (by simp))
    (memLp_step_apply c k q 2 (by simp))

theorem integrable_norm_sq_step (c : ℝ) (k : ℕ) :
    Integrable (fun ω : ℕ → EuclideanSpace ℝ ι => ‖step c k ω‖ ^ 2)
      (gaussPath (EuclideanSpace ℝ ι)) := by
  have he : (fun ω : ℕ → EuclideanSpace ℝ ι => ‖step c k ω‖ ^ 2)
      = fun ω : ℕ → EuclideanSpace ℝ ι => c ^ 2 * ‖coord k ω‖ ^ 2 := by
    funext ω
    rw [step, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [he]
  exact (integrable_norm_sq_coord k).const_mul _

/-! ### Reducing the two remaining Gaussian-side integrals to measurability -/

/-- `hintquad`: `κ‖π_k ξ_k‖²` is integrable as soon as it is a.e. strongly measurable, because
`‖π x‖ ≤ ‖x‖` and `‖ξ_k‖²` is integrable. -/
theorem integrable_quad_of_aestronglyMeasurable (c κ : ℝ) (k : ℕ)
    {K : ℕ → (ℕ → EuclideanSpace ℝ ι) → Submodule ℝ (EuclideanSpace ℝ ι)}
    [∀ k ω, (K k ω).HasOrthogonalProjection]
    (hm : AEStronglyMeasurable
      (fun ω : ℕ → EuclideanSpace ℝ ι => κ * ‖(K k ω).starProjection (step c k ω)‖ ^ 2)
      (gaussPath (EuclideanSpace ℝ ι))) :
    Integrable (fun ω : ℕ → EuclideanSpace ℝ ι =>
      κ * ‖(K k ω).starProjection (step c k ω)‖ ^ 2) (gaussPath (EuclideanSpace ℝ ι)) := by
  refine Integrable.mono' ((integrable_norm_sq_step c k).const_mul |κ|) hm ?_
  refine Filter.Eventually.of_forall fun ω => ?_
  have hle : ‖(K k ω).starProjection (step c k ω)‖ ≤ ‖step c k ω‖ :=
    Submodule.norm_starProjection_apply_le _ _
  have h0 : (0 : ℝ) ≤ ‖(K k ω).starProjection (step c k ω)‖ := norm_nonneg _
  have hsq : ‖(K k ω).starProjection (step c k ω)‖ ^ 2 ≤ ‖step c k ω‖ ^ 2 := by
    exact pow_le_pow_left₀ h0 hle 2
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤
    ‖(K k ω).starProjection (step c k ω)‖ ^ 2)]
  exact mul_le_mul_of_nonneg_left hsq (abs_nonneg κ)

/-- `hintK`: a coefficient bounded by `C` times a product of two coordinates is integrable as soon
as the coefficient is a.e. strongly measurable.  For `driftInputs_step_chain` the coefficient is
`(π_k e_p) q`, bounded by `‖π_k e_p‖ ≤ ‖e_p‖ = 1`. -/
theorem integrable_bddCoeff_mul (c : ℝ) (k : ℕ) (p q : ι)
    {M : (ℕ → EuclideanSpace ℝ ι) → ℝ} {C : ℝ}
    (hm : AEStronglyMeasurable M (gaussPath (EuclideanSpace ℝ ι)))
    (hC : ∀ ω, ‖M ω‖ ≤ C) :
    Integrable (fun ω : ℕ → EuclideanSpace ℝ ι => M ω * (step c k ω p * step c k ω q))
      (gaussPath (EuclideanSpace ℝ ι)) :=
  (integrable_step_mul c k p q).bdd_mul hm (Filter.Eventually.of_forall hC)

/-- A coordinate is bounded by the norm. -/
theorem norm_coord_le (x : EuclideanSpace ℝ ι) (q : ι) : ‖x q‖ ≤ ‖x‖ := by
  have h : x q = ⟪(EuclideanSpace.single q (1 : ℝ)), x⟫ :=
    (StepInputs2.inner_single_left' q x).symm
  have hn : ‖(EuclideanSpace.single q (1 : ℝ) : EuclideanSpace ℝ ι)‖ = 1 := by simp
  rw [Real.norm_eq_abs, h]
  refine le_trans (abs_real_inner_le_norm _ _) ?_
  rw [hn, one_mul]

/-- The bound `integrable_bddCoeff_mul` is applied at: an orthogonal projection's matrix entries
are at most `1` in absolute value. -/
theorem abs_starProjection_single_le_one (K : Submodule ℝ (EuclideanSpace ℝ ι))
    [K.HasOrthogonalProjection] (p q : ι) :
    ‖(K.starProjection (EuclideanSpace.single p (1 : ℝ))) q‖ ≤ 1 := by
  have h1 := norm_coord_le (K.starProjection (EuclideanSpace.single p (1 : ℝ))) q
  have h2 : ‖K.starProjection (EuclideanSpace.single p (1 : ℝ))‖
      ≤ ‖(EuclideanSpace.single p (1 : ℝ) : EuclideanSpace ℝ ι)‖ :=
    Submodule.norm_starProjection_apply_le _ _
  have h3 : ‖(EuclideanSpace.single p (1 : ℝ) : EuclideanSpace ℝ ι)‖ = 1 := by simp
  linarith

end Step

/-! ## 5. `driftInputs_step_chain`, instantiated on the path space -/

section Drift

variable {n : ℕ}

/-- **`StepInputs2.driftInputs_step_chain` on the path space.**  Every hypothesis *about the driving
sequence* is discharged here: measurability, the coordinate law at variance `c²`, the coordinates'
independence, the two Gaussian moments, the filtration with its `≤ mΩ` and `SigmaFinite` trim, and
the independence of each increment from its own past.  What remains are exactly the hypotheses
about the chain's own data `K`, `V`, `D`, `err`. -/
theorem driftInputs_step_path {c κ : ℝ} {m : ℕ}
    {K : ℕ → (ℕ → EuclideanSpace ℝ (UT n)) → Submodule ℝ (EuclideanSpace ℝ (UT n))}
    {V : ℕ → (ℕ → EuclideanSpace ℝ (UT n)) → EuclideanSpace ℝ (UT n)}
    {D err : ℕ → (ℕ → EuclideanSpace ℝ (UT n)) → ℝ}
    (hintV : ∀ k, ∀ p : UT n, Integrable (fun ω => V k ω p * step c k ω p)
      (gaussPath (EuclideanSpace ℝ (UT n))))
    (hintK : ∀ k, ∀ p q : UT n, Integrable (fun ω =>
      ((K k ω).starProjection (EuclideanSpace.single p (1 : ℝ))) q
        * (step c k ω p * step c k ω q)) (gaussPath (EuclideanSpace ℝ (UT n))))
    (hintD : ∀ k, Integrable (D k) (gaussPath (EuclideanSpace ℝ (UT n))))
    (hinttr : ∀ k, Integrable (fun ω => ⟪V k ω, step c k ω⟫)
      (gaussPath (EuclideanSpace ℝ (UT n))))
    (hintquad : ∀ k, Integrable (fun ω => κ * ‖(K k ω).starProjection (step c k ω)‖ ^ 2)
      (gaussPath (EuclideanSpace ℝ (UT n))))
    (hinterr : ∀ k, Integrable (err k) (gaussPath (EuclideanSpace ℝ (UT n))))
    (hVm : ∀ k, ∀ p : UT n, StronglyMeasurable[natFil k] fun ω => V k ω p)
    (hKm : ∀ k, ∀ p q : UT n, StronglyMeasurable[natFil k]
      fun ω => ((K k ω).starProjection (EuclideanSpace.single p (1 : ℝ))) q)
    (hDm : ∀ k, StronglyMeasurable[natFil k] (D k))
    (herrm : ∀ k, StronglyMeasurable[natFil k] (err k))
    (hpt : ∀ k, k < m → ∀ᵐ ω ∂(gaussPath (EuclideanSpace ℝ (UT n))), D (k + 1) ω ≤ D k ω
      + ⟪V k ω, step c k ω⟫
      - κ * ‖(K k ω).starProjection (step c k ω)‖ ^ 2 + err k ω) :
    ∀ k, k < m → (gaussPath (EuclideanSpace ℝ (UT n)))[D (k + 1)|natFil k]
      ≤ᵐ[gaussPath (EuclideanSpace ℝ (UT n))] fun ω =>
        D k ω - (κ * ((Real.toNNReal (c ^ 2) : ℝ≥0) : ℝ))
          * ((Module.finrank ℝ (K k ω) : ℕ) : ℝ) + err k ω :=
  StepInputs2.driftInputs_step_chain (ξ := step c) (v := Real.toNNReal (c ^ 2)) (c := κ)
    (fun k => measurable_step c k) (fun k => step_coord_indep c k)
    (fun k p => step_coord_law c k p)
    (fun k p => integrable_step_apply c k p) (fun k p q => integrable_step_mul c k p q)
    hintV hintK hintD hinttr hintquad hinterr natFil_le
    (fun k => indep_step_natFil c k) hVm hKm hDm herrm hpt

/-- **`hacc` on the path space.**  `StateInvariant4.measureReal_compl_accGood_le'` needs the
increment's law at scale `c` and the sequence's independence; both are `map_step` and
`iIndepFun_step`, so the accumulated event's cost is now a theorem with no probabilistic
hypothesis at all. -/
theorem measureReal_compl_accGood_path {ι : Type*} [DecidableEq ι] [Countable ι]
    {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
    {N : ℕ} {c r₀ s : ℝ} (hc : 0 < c) (hr₀ : 0 ≤ r₀) (hs : 1 ≤ s)
    (hthr : 6 * (Real.sqrt N * c) * s * Real.sqrt n ≤ r₀) :
    (gaussPath (EuclideanSpace ℝ (UT n))).real
        (StateInvariant.accGood q W A₀ (step c) N r₀)ᶜ
      ≤ (N : ℝ) * (2 * (4 * Real.exp (-(s ^ 2 * n)))) :=
  StateInvariant4.measureReal_compl_accGood_le' hc hr₀ hs (fun k => measurable_step c k)
    (iIndepFun_step c) (fun j => map_step c j) hthr

end Drift

/-! ## 6. `Theorem.ChainSetup`, constructed -/

section Setup

/-- **Residual B of report 46, discharged**: the space, the coordinates, their law, the filtration
and the independence of each increment from its past, all exhibited. -/
theorem chainSetup (n : ℕ) : Theorem.ChainSetup n :=
  ⟨⟨ℕ → EuclideanSpace ℝ (UT n), inferInstance,
    gaussPath (EuclideanSpace ℝ (UT n)), inferInstance, coord,
    fun k => measurable_coord k, fun k => map_coord k,
    natFil, monotone_natFil, fun k => indep_coord_natFil k⟩⟩

end Setup

/-! ## 7. The padding map on this space (brief 47's route addition)

Report 45 reduced the transported Proposition 4.1 to `hincl` — the padded increment vector's law —
and named the missing instantiation.  Here it is, on this space.  The point is that the fresh
coordinate is **not** a second factor: it is the second summand of the value type, so the chain
increment and the padding coordinate are one standard Gaussian and `hincl_of_padding` applies with
no reshuffling.  The external factor of `hprop_of_hincl`'s two-factor carrier then carries nothing
and integrates out by `hincl_prod`, which is exactly what that lemma was written for. -/

section Padding

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

omit [BorelSpace F] in
/-- `PaddingMap`'s `hpast`: the increment is independent of its own past. -/
theorem indepFun_pastOf_coord (k : ℕ) :
    IndepFun (pastOf (coord (F := F)) k) (coord k) (gaussPath F) := by
  have hg : Measurable fun v : Fin k → F => (fun j : ℕ => if h : j < k then v ⟨j, h⟩ else 0) := by
    refine Measurable.of_eval fun j => ?_
    by_cases h : j < k
    · simp only [dite_eq_left h]; exact measurable_pi_apply _
    · simp only [dite_eq_right h]; exact measurable_const
  have h := ((indepFun_coord_restr (F := F) k).symm).comp hg
    (measurable_id : Measurable (id : F → F))
  have e1 : ((fun v : Fin k → F => (fun j : ℕ => if h : j < k then v ⟨j, h⟩ else 0)) ∘ restr k)
      = pastOf (coord (F := F)) k := by
    funext ω
    funext j
    by_cases h : j < k
    · show (if h' : j < k then (restr k ω) ⟨j, h'⟩ else 0) = (if j < k then coord j ω else 0)
      rw [dite_eq_left h, ite_eq_left h]; rfl
    · show (if h' : j < k then (restr k ω) ⟨j, h'⟩ else 0) = (if j < k then coord j ω else 0)
      rw [dite_eq_right h, ite_eq_right h]
  have e2 : (id ∘ coord (F := F) k) = coord k := rfl
  rw [e1, e2] at h
  exact h

/-- **The completed unit direction** of report 45 §5: the past-measurable chain direction `w`
completed by the fresh direction `e` to a unit vector. -/
def padUnit (w e : F) : F := w + Real.sqrt (1 - ‖w‖ ^ 2) • e

omit [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
theorem norm_padUnit_eq_one {w e : F} (hw : ‖w‖ ≤ 1) (he : ‖e‖ = 1) (horth : ⟪w, e⟫ = 0) :
    ‖padUnit w e‖ = 1 := norm_padUnit hw he horth

theorem measurable_padUnit {w e : (ℕ → F) → F} (hw : Measurable w) (he : Measurable e) :
    Measurable fun p : ℕ → F => padUnit (w p) (e p) := by
  have hs : Measurable fun p : ℕ → F => Real.sqrt (1 - ‖w p‖ ^ 2) :=
    Real.continuous_sqrt.measurable.comp (measurable_const.sub (hw.norm.pow_const 2))
  exact hw.add (hs.smul he)

/-- **`hincl` at every horizon, on this space**: the padded increments are i.i.d. `N(0, r²)`. -/
theorem hincl_on_setup {r : ℝ} (dir : ℕ → (ℕ → F) → F) (hdir : ∀ k, Measurable (dir k))
    (hunit : ∀ k p, ‖dir k p‖ = 1) (N : ℕ) :
    (gaussPath F).map (fun ω (i : Fin N) => padInc r (coord (F := F)) dir (i : ℕ) ω)
      = Measure.pi fun _ : Fin N => gaussianReal 0 (Real.toNNReal (r ^ 2)) :=
  hincl_of_padding (fun j => measurable_coord j) hdir (fun k => map_coord k)
    (fun k => indepFun_pastOf_coord k) hunit N

/-- **The padded walk**: the process whose increments *are* the padded increments, so that the
padding needs no external coordinate. -/
def padWalk (r : ℝ) (dir : ℕ → (ℕ → F) → F) (M₀ : ℝ) (j : ℕ) (ω : ℕ → F) : ℝ :=
  M₀ - ∑ i ∈ Finset.range j, padInc r (coord (F := F)) dir i ω

theorem measurable_padWalk {r : ℝ} {dir : ℕ → (ℕ → F) → F} (hdir : ∀ k, Measurable (dir k))
    (M₀ : ℝ) (j : ℕ) : Measurable (padWalk r dir M₀ j) :=
  measurable_const.sub (Finset.measurable_sum _ fun i _ =>
    measurable_padInc (fun l => measurable_coord l) hdir i)

omit [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
theorem padWalk_zero (r : ℝ) (dir : ℕ → (ℕ → F) → F) (M₀ : ℝ) (ω : ℕ → F) :
    padWalk r dir M₀ 0 ω = M₀ := by simp [padWalk]

omit [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
theorem padIncVec_padWalk (r : ℝ) (dir : ℕ → (ℕ → F) → F) (M₀ : ℝ) (N : ℕ)
    (ω : (ℕ → F) × (Fin N → ℝ)) :
    padIncVec (padWalk r dir M₀) (fun _ _ => (0 : ℝ)) N ω
      = fun i : Fin N => padInc r (coord (F := F)) dir (i : ℕ) ω.1 := by
  funext i
  show -((padWalk r dir M₀ ((i : ℕ) + 1) ω.1 - padWalk r dir M₀ (i : ℕ) ω.1) + 0 * ω.2 i)
      = padInc r (coord (F := F)) dir (i : ℕ) ω.1
  rw [padWalk, padWalk, Finset.sum_range_succ]
  ring

/-- **`padded_law_on_setup`** — the padded increment vector's law on this space, in the exact shape
`WalkTelescope.hprop_of_hincl` consumes.  The external factor carries nothing and integrates out by
`hincl_prod`. -/
theorem padded_law_on_setup {r : ℝ} (dir : ℕ → (ℕ → F) → F) (hdir : ∀ k, Measurable (dir k))
    (hunit : ∀ k p, ‖dir k p‖ = 1) (M₀ : ℝ) (N : ℕ) :
    ((gaussPath F).prod
        (Measure.pi fun _ : Fin N => gaussianReal 0 (Real.toNNReal (r ^ 2)))).map
        (padIncVec (padWalk r dir M₀) (fun _ _ => (0 : ℝ)) N)
      = Measure.pi fun _ : Fin N => gaussianReal 0 (Real.toNNReal (r ^ 2)) := by
  have he : (padIncVec (padWalk r dir M₀) (fun _ _ => (0 : ℝ)) N)
      = fun q : (ℕ → F) × (Fin N → ℝ) =>
          fun i : Fin N => padInc r (coord (F := F)) dir (i : ℕ) q.1 :=
    funext fun ω => padIncVec_padWalk r dir M₀ N ω
  rw [he]
  exact hincl_prod (fun i => padInc r (coord (F := F)) dir i)
    (fun i => measurable_padInc (fun l => measurable_coord l) hdir i)
    (hincl_on_setup dir hdir hunit N)

/-- **The transported Proposition 4.1 on this space, with no probabilistic hypothesis left.**
Only the direction family's measurability and unit norm, and the numeric variance identity, remain
— and `norm_padUnit_eq_one` supplies the second from the completed direction. -/
theorem tail_on_setup {r : ℝ} (dir : ℕ → (ℕ → F) → F) (hdir : ∀ k, Measurable (dir k))
    (hunit : ∀ k p, ‖dir k p‖ = 1) {N : ℕ} {a₀ u t : ℝ} (ht : 0 < t)
    (hM₀ : 0 < a₀ - (u ^ 2)⁻¹)
    (hv : ((N • Real.toNNReal (r ^ 2) : ℝ≥0) : ℝ) = t * 1 ^ 2) :
    (gaussPath F) {ω | ∃ j ≤ N, padWalk r dir (a₀ - (u ^ 2)⁻¹) j ω ≤ 0}
      ≤ ENNReal.ofReal (4 * Phi (yOf a₀ t u)) :=
  hprop_of_hincl (measurable_padWalk hdir _) (fun _ => measurable_const) ht hM₀
    (fun ω => padWalk_zero r dir _ ω) hv (padded_law_on_setup dir hdir hunit _ N)

end Padding

/-! ### The two-factor carrier, with the fresh coordinate as the second summand -/

section TwoFactor

variable {n : ℕ}

/-- **The two-factor carrier**: the chain's increment and the padding's fresh coordinate, read as
*one* standard Gaussian.  This is report 45 §5's `WithLp 2 (E × ℝ)`. -/
abbrev PadCarrier (n : ℕ) : Type := WithLp 2 (EuclideanSpace ℝ (UT n) × ℝ)

/-- The chain direction, in the first summand. -/
def chainDir (v : EuclideanSpace ℝ (UT n)) : PadCarrier n := WithLp.toLp 2 (v, 0)

/-- The fresh direction: the second summand's unit vector. -/
def freshDir (n : ℕ) : PadCarrier n := WithLp.toLp 2 (0, 1)

theorem inner_chainDir_freshDir (v : EuclideanSpace ℝ (UT n)) :
    ⟪chainDir v, freshDir n⟫ = 0 := by
  simp [chainDir, freshDir]

theorem norm_chainDir (v : EuclideanSpace ℝ (UT n)) : ‖chainDir v‖ = ‖v‖ := by
  have h : ‖chainDir v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2]; simp [chainDir]
  have h0 : (0 : ℝ) ≤ ‖chainDir v‖ := norm_nonneg _
  nlinarith [norm_nonneg v]

theorem norm_freshDir (n : ℕ) : ‖freshDir n‖ = 1 := by
  have h : ‖freshDir n‖ ^ 2 = 1 := by
    rw [WithLp.prod_norm_sq_eq_of_L2]; simp [freshDir]
  nlinarith [norm_nonneg (freshDir n)]

theorem measurable_chainDir : Measurable (chainDir (n := n)) :=
  (WithLp.measurable_toLp _ _).comp (measurable_id.prodMk measurable_const)

/-- **The completed unit direction at the two-factor carrier** — report 45 §5's `u_i`. -/
def padDir (w : ℕ → (ℕ → PadCarrier n) → EuclideanSpace ℝ (UT n)) (k : ℕ)
    (p : ℕ → PadCarrier n) : PadCarrier n :=
  padUnit (chainDir (w k p)) (freshDir n)

theorem norm_padDir_eq_one {w : ℕ → (ℕ → PadCarrier n) → EuclideanSpace ℝ (UT n)}
    (hw : ∀ k p, ‖w k p‖ ≤ 1) (k : ℕ) (p : ℕ → PadCarrier n) : ‖padDir w k p‖ = 1 :=
  norm_padUnit_eq_one (by rw [norm_chainDir]; exact hw k p) (norm_freshDir n)
    (inner_chainDir_freshDir _)

theorem measurable_padDir {w : ℕ → (ℕ → PadCarrier n) → EuclideanSpace ℝ (UT n)}
    (hwm : ∀ k, Measurable (w k)) (k : ℕ) : Measurable (padDir w k) :=
  measurable_padUnit (measurable_chainDir.comp (hwm k)) measurable_const

/-- **The padded increment, written out.**  `r·(⟪ξ_k, w_k⟫ + √(1 − ‖w_k‖²)·η_k)` — Klartag's padded
increment exactly, with `η_k` the fresh coordinate. -/
theorem padInc_padDir (r : ℝ) (w : ℕ → (ℕ → PadCarrier n) → EuclideanSpace ℝ (UT n)) (k : ℕ)
    (ω : ℕ → PadCarrier n) :
    padInc r (coord (F := PadCarrier n)) (padDir w) k ω
      = r * (⟪(WithLp.ofLp (coord k ω)).1, w k (pastOf coord k ω)⟫
        + (WithLp.ofLp (coord k ω)).2 * Real.sqrt (1 - ‖w k (pastOf coord k ω)‖ ^ 2)) := by
  show r * ⟪coord k ω, padDir w k (pastOf coord k ω)⟫ = _
  rw [padDir, padUnit, WithLp.prod_inner_apply]
  simp [chainDir, freshDir]
  exact Or.inl (mul_comm _ _)

/-- **The tail on the two-factor carrier, with the completed direction supplied** — no hypothesis
beyond the chain direction's measurability, its norm bound, and the numeric variance identity. -/
theorem tail_on_padCarrier {r : ℝ} {w : ℕ → (ℕ → PadCarrier n) → EuclideanSpace ℝ (UT n)}
    (hwm : ∀ k, Measurable (w k)) (hw1 : ∀ k p, ‖w k p‖ ≤ 1)
    {N : ℕ} {a₀ u t : ℝ} (ht : 0 < t) (hM₀ : 0 < a₀ - (u ^ 2)⁻¹)
    (hv : ((N • Real.toNNReal (r ^ 2) : ℝ≥0) : ℝ) = t * 1 ^ 2) :
    (gaussPath (PadCarrier n))
        {ω | ∃ j ≤ N, padWalk r (padDir w) (a₀ - (u ^ 2)⁻¹) j ω ≤ 0}
      ≤ ENNReal.ofReal (4 * Phi (yOf a₀ t u)) :=
  tail_on_setup (padDir w) (measurable_padDir hwm) (norm_padDir_eq_one hw1) ht hM₀ hv

end TwoFactor

end

end Submission.L10.ChainSetup

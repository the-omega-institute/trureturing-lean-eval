import Submission.L10.LogDetVariance

/-!
# Gate L-10 (`klartag_packing`), brief 96a — the martingale part of the stopped log-determinant

Brief 94a item (3): the per-step conditional second moment `LogDetVariance.condExp_inner_sq` has to
become a bound on the second moment of the **sum**
`M_K = ∑_{k<K} ⟪V_k, ξ_k⟫`, `V_k = DriftStopped.stoppedV …` the stopped `π_k(matToUT A_k⁻¹)`.
Orthogonality of the increments does it, and the obstruction was never the algebra but the
side conditions at the chain's own `V_k`.

Those side conditions are **already in the tree** — `DriftInputsStopped` spent them on the drift
record — and this module reuses them rather than re-deriving:

* `DriftInputsStopped.stronglyMeasurable_stoppedV_coord` — each coordinate of `V_k` is
  `ℱ k`-measurable;
* `DriftInputsStopped.abs_stoppedV_coord_le` — each coordinate is bounded by `√n/m`, **everywhere**
  (`StoppedChain.stateBounds_stopped` holds on every path), which is what makes every product
  integrable by domination;
* `ChainSetup.indep_step_natFil`, `step_coord_law`, `integrable_step_mul`, `integrable_bddCoeff_mul`
  — the increment's law, independence of the past, and the two integrability workhorses;
* `StepInputs2.condExp_inner_eq_zero`, `StepInputs2.integral_coord_mul`, and 94a's
  `LogDetVariance.condExp_inner_sq`.

Rule 23 applies throughout: `letI : MeasurableSpace Ω := mΩ` before any `Integrable … P` in a
context carrying a filtration.

## Contents

1. `mgIncr`, `mgPart` — the increment and the partial sums.
2. The side conditions: measurability at `ℱ (k+1)`, integrability of `mgIncr`, of its square, and
   of the cross products.
3. `condExp_mgIncr_zero` — `E[Δ_k | ℱ_k] = 0`.
4. `integral_mgIncr_mul_eq_zero` — `E[Δ_j Δ_k] = 0` for `j < k`, by the tower property.
5. `integral_mgIncr_sq_le` — `E[Δ_k²] ≤ h·n/m²`.
6. `variance_M_le` — `E[(M_N)²] ≤ LogDetVariance.varBound n c₃`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Submission.L10.LogDetMartingale

open MeasureTheory Matrix Finset Module ProbabilityTheory
open scoped NNReal RealInnerProductSpace
open Submission.L10 Submission.L10.Increments
open Submission.L10.StoppedChain Submission.L10.DriftStopped
open Submission.L10.DriftInputsStopped

/-! ## 1. The increment and the partial sums -/

section Defs

variable {n : ℕ} {ι : Type*} [DecidableEq ι] {Ω : Type*} [MeasurableSpace Ω]

/-- **The martingale increment** `Δ_k = ⟪V_k, ξ_k⟫`, with `V_k` the *stopped* `π_k(A_k⁻¹)`. -/
noncomputable def mgIncr (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι)
    (A₀ : EuclideanSpace ℝ (UT n)) (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n))
    (η r₀ c₃ : ℝ) (N k : ℕ) (ω : Ω) : ℝ :=
  ⟪stoppedV q W A₀ ξ η r₀ c₃ N k ω, ξ k ω⟫

/-- **The martingale** `M_K = ∑_{k<K} Δ_k`. -/
noncomputable def mgPart (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι)
    (A₀ : EuclideanSpace ℝ (UT n)) (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n))
    (η r₀ c₃ : ℝ) (N K : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range K, mgIncr q W A₀ ξ η r₀ c₃ N k ω

theorem mgIncr_eq_sum (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι)
    (A₀ : EuclideanSpace ℝ (UT n)) (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n))
    (η r₀ c₃ : ℝ) (N k : ℕ) (ω : Ω) :
    mgIncr q W A₀ ξ η r₀ c₃ N k ω
      = ∑ p : UT n, stoppedV q W A₀ ξ η r₀ c₃ N k ω p * ξ k ω p := by
  rw [mgIncr]
  simp [PiLp.inner_apply, mul_comm]

end Defs

/-! ## 2. The side conditions at the chain -/

section Side

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}

/-- Each coordinate of `V_k` is `ℱ k`-measurable, at the chain's own filtration. -/
theorem stronglyMeasurable_V_coord (cstep η r₀ c₃ : ℝ) (N k : ℕ) (p : UT n) :
    StronglyMeasurable[ChainSetup.filtration (F := EuclideanSpace ℝ (UT n)) k]
      fun ω => stoppedV q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω p :=
  stronglyMeasurable_stoppedV_coord (ChainSetup.filtration (F := EuclideanSpace ℝ (UT n)))
    (fun j => measurable_step_natFil cstep j)
    (fun j => measurableSet_stateGood_step cstep η r₀ c₃ j) N k p

/-- `Δ_k` is `ℱ (k+1)`-measurable: `V_k` is `ℱ k`-measurable and `ξ_k` is `ℱ (k+1)`-measurable. -/
theorem stronglyMeasurable_mgIncr (cstep η r₀ c₃ : ℝ) (N k : ℕ) :
    StronglyMeasurable[ChainSetup.filtration (F := EuclideanSpace ℝ (UT n)) (k + 1)]
      (mgIncr q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k) := by
  classical
  have hmono : ChainSetup.filtration (F := EuclideanSpace ℝ (UT n)) k
      ≤ ChainSetup.filtration (F := EuclideanSpace ℝ (UT n)) (k + 1) :=
    (ChainSetup.filtration (F := EuclideanSpace ℝ (UT n))).mono (Nat.le_succ k)
  have hrep : mgIncr q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k
      = fun ω => ∑ p : UT n,
          stoppedV q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω p
            * ChainSetup.step cstep k ω p :=
    funext fun ω => mgIncr_eq_sum _ _ _ _ _ _ _ _ _ _
  rw [hrep]
  refine Measurable.stronglyMeasurable ?_
  refine Finset.measurable_sum (Finset.univ : Finset (UT n)) fun p _ => ?_
  have hξp : Measurable[ChainSetup.filtration (F := EuclideanSpace ℝ (UT n)) (k + 1)]
      fun ω => ChainSetup.step cstep k ω p :=
    ((measurable_pi_apply p).comp (WithLp.measurable_ofLp _ _)).comp
      (measurable_step_natFil cstep k)
  exact Measurable.mul
    ((stronglyMeasurable_V_coord cstep η r₀ c₃ N k p).mono hmono).measurable hξp

/-- `|Δ_k| ≤ (√n/m)·‖ξ_k‖` — Cauchy–Schwarz against `DriftStopped2.norm_stoppedV_le`, which holds
on **every** path. -/
theorem abs_mgIncr_le {Ω : Type*} [MeasurableSpace Ω] {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}
    {η a₀ r₀ c₃ : ℝ} {N : ℕ} (hN : 1 ≤ N) (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃) (hlt : r₀ + c₃ * η < a₀) (k : ℕ) (ω : Ω) :
    |mgIncr q W A₀ ξ η r₀ c₃ N k ω|
      ≤ (Real.sqrt n / (a₀ - (r₀ + c₃ * η))) * ‖ξ k ω‖ := by
  refine le_trans (abs_real_inner_le_norm _ _) ?_
  exact mul_le_mul_of_nonneg_right
    (DriftStopped2.norm_stoppedV_le hN hA₀ hq hne hA₀m hη hr₀ hc₃ hlt k ω) (norm_nonneg _)

theorem aestronglyMeasurable_mgIncr (cstep η r₀ c₃ : ℝ) (N k : ℕ) :
    AEStronglyMeasurable (mgIncr q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k)
      (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) :=
  ((stronglyMeasurable_mgIncr cstep η r₀ c₃ N k).mono
    (ChainSetup.natFil_le (k + 1))).aestronglyMeasurable

/-- `Δ_k² ≤ (n/m²)‖ξ_k‖²`, so `Δ_k` is square-integrable. -/
theorem integrable_mgIncr_sq {cstep η a₀ r₀ c₃ : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃) (hlt : r₀ + c₃ * η < a₀) (k : ℕ) :
    Integrable (fun ω => (mgIncr q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω) ^ 2)
      (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) := by
  set C : ℝ := Real.sqrt n / (a₀ - (r₀ + c₃ * η)) with hC
  have hm : 0 < a₀ - (r₀ + c₃ * η) := by linarith
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  refine Integrable.mono' ((ChainSetup.integrable_norm_sq_step cstep k).const_mul (C ^ 2))
    ((aestronglyMeasurable_mgIncr cstep η r₀ c₃ N k).pow 2)
    (Filter.Eventually.of_forall fun ω => ?_)
  have hb := abs_mgIncr_le (ξ := ChainSetup.step cstep) hN hA₀ hq hne hA₀m hη hr₀ hc₃ hlt k ω
  have habs : (0 : ℝ) ≤ |mgIncr q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω| := abs_nonneg _
  have hsq : (mgIncr q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω) ^ 2
      = |mgIncr q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω| ^ 2 := (sq_abs _).symm
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤
    (mgIncr q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω) ^ 2), hsq]
  nlinarith [hb, habs, norm_nonneg (ChainSetup.step cstep k ω), hC0]

theorem memLp_two_mgIncr {cstep η a₀ r₀ c₃ : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃) (hlt : r₀ + c₃ * η < a₀) (k : ℕ) :
    MemLp (mgIncr q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k) 2
      (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) :=
  (memLp_two_iff_integrable_sq (aestronglyMeasurable_mgIncr cstep η r₀ c₃ N k)).2
    (integrable_mgIncr_sq hN hA₀ hq hne hA₀m hη hr₀ hc₃ hlt k)

theorem integrable_mgIncr {cstep η a₀ r₀ c₃ : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃) (hlt : r₀ + c₃ * η < a₀) (k : ℕ) :
    Integrable (mgIncr q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k)
      (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) :=
  (memLp_two_mgIncr hN hA₀ hq hne hA₀m hη hr₀ hc₃ hlt k).integrable (by norm_num)

/-- Every product of two increments is integrable — `L² × L² ⊆ L¹`. -/
theorem integrable_mgIncr_mul {cstep η a₀ r₀ c₃ : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃) (hlt : r₀ + c₃ * η < a₀) (j k : ℕ) :
    Integrable (fun ω => mgIncr q W A₀ (ChainSetup.step cstep) η r₀ c₃ N j ω
        * mgIncr q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω)
      (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) :=
  MemLp.integrable_mul (memLp_two_mgIncr hN hA₀ hq hne hA₀m hη hr₀ hc₃ hlt j)
    (memLp_two_mgIncr hN hA₀ hq hne hA₀m hη hr₀ hc₃ hlt k)

end Side

/-! ## 3. The increment is a martingale difference -/

section Mart

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}

/-- **`E[Δ_k | ℱ_k] = 0`** — `StepInputs2.condExp_inner_eq_zero` at the chain's own `V_k`, exactly
as `DriftInputsStopped.driftInputs_step_stopped` uses it for the drift. -/
theorem condExp_mgIncr_zero {cstep η a₀ r₀ c₃ : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃) (hlt : r₀ + c₃ * η < a₀) (k : ℕ) :
    (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))[
        mgIncr q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k
        | ChainSetup.filtration (F := EuclideanSpace ℝ (UT n)) k]
      =ᵐ[ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))] 0 := by
  classical
  have hVm := fun p => stronglyMeasurable_V_coord (q := q) (W := W) (A₀ := A₀) cstep η r₀ c₃ N k p
  have hintV : ∀ p : UT n, Integrable (fun ω =>
      stoppedV q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω p * ChainSetup.step cstep k ω p)
      (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) := by
    intro p
    exact (ChainSetup.integrable_step_apply cstep k p).bdd_mul
      (c := Real.sqrt n / (a₀ - (r₀ + c₃ * η)))
      ((hVm p).mono (ChainSetup.natFil_le k)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω =>
        abs_stoppedV_coord_le hN hA₀ hq hne hA₀m hη hr₀ hc₃ hlt k ω p)
  exact StepInputs2.condExp_inner_eq_zero (ChainSetup.natFil_le k) hVm
    (ChainSetup.measurable_step cstep k) (ChainSetup.indep_step_natFil cstep k)
    (fun p => StepInputs2.integral_coord_eq_zero (ChainSetup.measurable_step cstep k)
      (fun r => ChainSetup.step_coord_law cstep k r) p)
    (fun p => ChainSetup.integrable_step_apply cstep k p) hintV

/-- **Orthogonality.**  `E[Δ_j Δ_k] = 0` for `j < k`: `Δ_j` is `ℱ k`-measurable (it reads `V_j` at
`ℱ j` and `ξ_j` at `ℱ (j+1) ≤ ℱ k`), so it pulls out of the conditional expectation and what is
left is `E[Δ_k | ℱ_k] = 0`. -/
theorem integral_mgIncr_mul_eq_zero {cstep η a₀ r₀ c₃ : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃) (hlt : r₀ + c₃ * η < a₀)
    {j k : ℕ} (hjk : j < k) :
    ∫ ω, mgIncr q W A₀ (ChainSetup.step cstep) η r₀ c₃ N j ω
        * mgIncr q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω
      ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) = 0 := by
  classical
  have hjm : StronglyMeasurable[ChainSetup.filtration (F := EuclideanSpace ℝ (UT n)) k]
      (mgIncr q W A₀ (ChainSetup.step cstep) η r₀ c₃ N j) :=
    (stronglyMeasurable_mgIncr cstep η r₀ c₃ N j).mono
      ((ChainSetup.filtration (F := EuclideanSpace ℝ (UT n))).mono (by omega))
  have hprod := integrable_mgIncr_mul (q := q) (W := W) (A₀ := A₀) (cstep := cstep)
    hN hA₀ hq hne hA₀m hη hr₀ hc₃ hlt j k
  have hgk := integrable_mgIncr (q := q) (W := W) (A₀ := A₀) (cstep := cstep)
    hN hA₀ hq hne hA₀m hη hr₀ hc₃ hlt k
  have hpull := condExp_mul_of_stronglyMeasurable_left (m := ChainSetup.filtration
      (F := EuclideanSpace ℝ (UT n)) k) hjm hprod hgk
  have hzero := condExp_mgIncr_zero (q := q) (W := W) (A₀ := A₀) (cstep := cstep)
    hN hA₀ hq hne hA₀m hη hr₀ hc₃ hlt k
  have hcond : (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))[
      fun ω => mgIncr q W A₀ (ChainSetup.step cstep) η r₀ c₃ N j ω
        * mgIncr q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω
      | ChainSetup.filtration (F := EuclideanSpace ℝ (UT n)) k]
      =ᵐ[ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))] 0 := by
    refine hpull.trans ?_
    filter_upwards [hzero] with ω h2
    simp only [Pi.mul_apply, Pi.zero_apply] at h2 ⊢
    rw [h2, mul_zero]
  calc ∫ ω, mgIncr q W A₀ (ChainSetup.step cstep) η r₀ c₃ N j ω
        * mgIncr q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω
        ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))
      = ∫ ω, ((ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))[
          fun ω => mgIncr q W A₀ (ChainSetup.step cstep) η r₀ c₃ N j ω
            * mgIncr q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω
          | ChainSetup.filtration (F := EuclideanSpace ℝ (UT n)) k]) ω
          ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) :=
        (integral_condExp (ChainSetup.natFil_le k)).symm
    _ = 0 := by
        rw [integral_congr_ae hcond]
        simp

end Mart

/-! ## 4. The per-step second moment -/

section Second

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}

/-- **`E[Δ_k²] ≤ h·n/m²`.**  94a's `LogDetVariance.condExp_inner_sq` gives `E[Δ_k² | ℱ_k] = h‖V_k‖²`
— the *isotropy* is what saves the factor `dim`; the pointwise bound `|Δ_k| ≤ ‖V_k‖‖ξ_k‖` would
cost `h·d·n/m²` instead — and `DriftStopped2.norm_stoppedV_le` bounds `‖V_k‖² ≤ n/m²`. -/
theorem integral_mgIncr_sq_le {cstep η a₀ r₀ c₃ : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃) (hlt : r₀ + c₃ * η < a₀) (k : ℕ) :
    ∫ ω, (mgIncr q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω) ^ 2
        ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))
      ≤ cstep ^ 2 * ((n : ℝ) / (a₀ - (r₀ + c₃ * η)) ^ 2) := by
  classical
  have hm : 0 < a₀ - (r₀ + c₃ * η) := by linarith
  have hVm := fun p => stronglyMeasurable_V_coord (q := q) (W := W) (A₀ := A₀) cstep η r₀ c₃ N k p
  have hv : ((Real.toNNReal (cstep ^ 2) : ℝ≥0) : ℝ) = cstep ^ 2 :=
    Real.coe_toNNReal _ (sq_nonneg _)
  have hcov : ∀ p r : UT n,
      ∫ ω, ChainSetup.step cstep k ω p * ChainSetup.step cstep k ω r
        ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))
      = if p = r then cstep ^ 2 else 0 := by
    intro p r
    rw [StepInputs2.integral_coord_mul (ChainSetup.measurable_step cstep k)
      (ChainSetup.step_coord_indep cstep k) (fun t => ChainSetup.step_coord_law cstep k t) p r, hv]
  have hbdd : ∀ (p r : UT n) (ω : ℕ → EuclideanSpace ℝ (UT n)),
      ‖stoppedV q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω p
        * stoppedV q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω r‖
      ≤ (Real.sqrt n / (a₀ - (r₀ + c₃ * η))) ^ 2 := by
    intro p r ω
    have h1 := abs_stoppedV_coord_le (ξ := ChainSetup.step cstep)
      hN hA₀ hq hne hA₀m hη hr₀ hc₃ hlt k ω p
    have h2 := abs_stoppedV_coord_le (ξ := ChainSetup.step cstep)
      hN hA₀ hq hne hA₀m hη hr₀ hc₃ hlt k ω r
    rw [Real.norm_eq_abs, abs_mul]
    have h3 : (0 : ℝ) ≤ |stoppedV q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω p| := abs_nonneg _
    have h4 : (0 : ℝ) ≤ |stoppedV q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω r| := abs_nonneg _
    have h5 : (0 : ℝ) ≤ Real.sqrt n / (a₀ - (r₀ + c₃ * η)) := by positivity
    have hsq : (Real.sqrt n / (a₀ - (r₀ + c₃ * η))) ^ 2
        = (Real.sqrt n / (a₀ - (r₀ + c₃ * η))) * (Real.sqrt n / (a₀ - (r₀ + c₃ * η))) := sq _
    rw [hsq]
    exact mul_le_mul h1 h2 h4 h5
  have hint : ∀ p r : UT n, Integrable (fun ω =>
      (stoppedV q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω p
        * stoppedV q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω r)
      * (ChainSetup.step cstep k ω p * ChainSetup.step cstep k ω r))
      (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) := by
    intro p r
    exact ChainSetup.integrable_bddCoeff_mul cstep k p r
      ((((hVm p).mono (ChainSetup.natFil_le k)).mul
        ((hVm r).mono (ChainSetup.natFil_le k))).aestronglyMeasurable) (hbdd p r)
  have hcond := LogDetVariance.condExp_inner_sq
    (V := stoppedV q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k)
    (ξ := ChainSetup.step cstep k) (v := cstep ^ 2)
    (ChainSetup.measurable_step cstep k) hcov
    (fun p r => ChainSetup.integrable_step_mul cstep k p r) hint
    (ChainSetup.natFil_le k) hVm (ChainSetup.indep_step_natFil cstep k)
  have hfint : Integrable (fun ω => cstep ^ 2
      * ‖stoppedV q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω‖ ^ 2)
      (ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) :=
    integrable_condExp.congr hcond
  have hVsq : ∀ ω : ℕ → EuclideanSpace ℝ (UT n),
      ‖stoppedV q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω‖ ^ 2
        ≤ (n : ℝ) / (a₀ - (r₀ + c₃ * η)) ^ 2 := by
    intro ω
    have h1 := DriftStopped2.norm_stoppedV_le (ξ := ChainSetup.step cstep)
      hN hA₀ hq hne hA₀m hη hr₀ hc₃ hlt k ω
    have h2 : (0 : ℝ) ≤ ‖stoppedV q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω‖ := norm_nonneg _
    have h3 : (Real.sqrt n / (a₀ - (r₀ + c₃ * η))) ^ 2 = (n : ℝ) / (a₀ - (r₀ + c₃ * η)) ^ 2 := by
      rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    nlinarith [h1, h2, h3]
  calc ∫ ω, (mgIncr q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω) ^ 2
        ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))
      = ∫ ω, ((ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))[
          fun ω => (mgIncr q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω) ^ 2
          | ChainSetup.filtration (F := EuclideanSpace ℝ (UT n)) k]) ω
          ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) :=
        (integral_condExp (ChainSetup.natFil_le k)).symm
    _ = ∫ ω, cstep ^ 2 * ‖stoppedV q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω‖ ^ 2
          ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) := integral_congr_ae hcond
    _ ≤ ∫ _ω : ℕ → EuclideanSpace ℝ (UT n), cstep ^ 2 * ((n : ℝ) / (a₀ - (r₀ + c₃ * η)) ^ 2)
          ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) := by
        refine integral_mono_ae hfint (integrable_const _)
          (Filter.Eventually.of_forall fun ω => ?_)
        exact mul_le_mul_of_nonneg_left (hVsq ω) (sq_nonneg _)
    _ = cstep ^ 2 * ((n : ℝ) / (a₀ - (r₀ + c₃ * η)) ^ 2) := by simp

end Second

/-! ## 5. The martingale's second moment -/

section Var

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}

/-- **`E[(M_K)²] ≤ K·h·n/m²`.**  Expand the square into a double sum, kill every off-diagonal term
by orthogonality (§3), and price each diagonal term by §4.  `E[M_K] = 0`, so this is the variance. -/
theorem integral_mgPart_sq_le {cstep η a₀ r₀ c₃ : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃) (hlt : r₀ + c₃ * η < a₀) (K : ℕ) :
    ∫ ω, (mgPart q W A₀ (ChainSetup.step cstep) η r₀ c₃ N K ω) ^ 2
        ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))
      ≤ (K : ℝ) * (cstep ^ 2 * ((n : ℝ) / (a₀ - (r₀ + c₃ * η)) ^ 2)) := by
  classical
  have hmul := fun j k => integrable_mgIncr_mul (q := q) (W := W) (A₀ := A₀) (cstep := cstep)
    (N := N) hN hA₀ hq hne hA₀m hη hr₀ hc₃ hlt j k
  have horth := fun {j k : ℕ} (h : j < k) =>
    integral_mgIncr_mul_eq_zero (q := q) (W := W) (A₀ := A₀) (cstep := cstep) (N := N)
      hN hA₀ hq hne hA₀m hη hr₀ hc₃ hlt h
  have hexp : (fun ω => (mgPart q W A₀ (ChainSetup.step cstep) η r₀ c₃ N K ω) ^ 2)
      = fun ω => ∑ j ∈ Finset.range K, ∑ k ∈ Finset.range K,
          mgIncr q W A₀ (ChainSetup.step cstep) η r₀ c₃ N j ω
            * mgIncr q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω := by
    funext ω
    rw [mgPart, sq, Finset.sum_mul_sum]
  rw [hexp, integral_finsetSum _ (fun j _ => integrable_finsetSum _ fun k _ => hmul j k)]
  have hinner : ∀ j ∈ Finset.range K,
      ∫ ω, ∑ k ∈ Finset.range K,
          mgIncr q W A₀ (ChainSetup.step cstep) η r₀ c₃ N j ω
            * mgIncr q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω
          ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))
        = ∫ ω, (mgIncr q W A₀ (ChainSetup.step cstep) η r₀ c₃ N j ω) ^ 2
          ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) := by
    intro j hj
    rw [integral_finsetSum _ (fun k _ => hmul j k)]
    have hsingle : ∑ k ∈ Finset.range K,
        ∫ ω, mgIncr q W A₀ (ChainSetup.step cstep) η r₀ c₃ N j ω
            * mgIncr q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω
            ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))
        = ∫ ω, mgIncr q W A₀ (ChainSetup.step cstep) η r₀ c₃ N j ω
            * mgIncr q W A₀ (ChainSetup.step cstep) η r₀ c₃ N j ω
            ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n))) := by
      refine Finset.sum_eq_single j ?_ ?_
      · intro k _ hkj
        rcases lt_or_gt_of_ne hkj with h | h
        · have hswap : (fun ω => mgIncr q W A₀ (ChainSetup.step cstep) η r₀ c₃ N j ω
              * mgIncr q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω)
              = fun ω => mgIncr q W A₀ (ChainSetup.step cstep) η r₀ c₃ N k ω
                * mgIncr q W A₀ (ChainSetup.step cstep) η r₀ c₃ N j ω :=
            funext fun ω => mul_comm _ _
          rw [hswap]
          exact horth h
        · exact horth h
      · intro hjn
        exact absurd hj hjn
    rw [hsingle]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => (sq _).symm)
  rw [Finset.sum_congr rfl hinner]
  calc ∑ j ∈ Finset.range K, ∫ ω, (mgIncr q W A₀ (ChainSetup.step cstep) η r₀ c₃ N j ω) ^ 2
        ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))
      ≤ ∑ _j ∈ Finset.range K, cstep ^ 2 * ((n : ℝ) / (a₀ - (r₀ + c₃ * η)) ^ 2) :=
        Finset.sum_le_sum fun j _ =>
          integral_mgIncr_sq_le (q := q) (W := W) (A₀ := A₀) (cstep := cstep) (N := N)
            hN hA₀ hq hne hA₀m hη hr₀ hc₃ hlt j
    _ = (K : ℝ) * (cstep ^ 2 * ((n : ℝ) / (a₀ - (r₀ + c₃ * η)) ^ 2)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **The deliverable: `E[(M_N)²] ≤ LogDetVariance.varBound n c₃`.**  At the adopted parameters
`cAdopted n ² = h`, `a₀ − (r₀ + c₃η) = GoodPathBounds.mAt n c₃`, and `N·h = ChainDrift.horizon n`
exactly (`ParamsAdopted2.numStepsAdopted2_mul_stepSizeAdopted2`), so the `K·h·n/m²` of
`integral_mgPart_sq_le` is `T·n/m²` on the nose.  `LogDetVariance.varBound_le` then gives
`≤ 64·log n/n`, uniform in `n ≥ n₁` and in every admissible `c₃`. -/
theorem variance_M_le (hn : 2073600 ≤ n) {c₃ : ℝ} (hc₃0 : 0 ≤ c₃)
    (hc₃η : c₃ * DriftStopped6.etaAdopted n ≤ 1 / 4)
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a0C n • (1 : Matrix (Fin n) (Fin n) ℝ)) :
    ∫ ω, (mgPart q W A₀ (ChainSetup.step (Submission.L10.cAdopted n))
        (DriftStopped6.etaAdopted n) (DriftStopped6.r0Adopted n) c₃
        (ParamsAdopted2.numStepsAdopted2 n) (ParamsAdopted2.numStepsAdopted2 n) ω) ^ 2
        ∂(ChainSetup.gaussPath (EuclideanSpace ℝ (UT n)))
      ≤ LogDetVariance.varBound n c₃ := by
  have hn3 : 3 ≤ n := by omega
  have hN : 1 ≤ ParamsAdopted2.numStepsAdopted2 n := by
    have := Submission.L10.three_le_numStepsAdopted2 hn3; omega
  have hlt := GoodPathBounds.lt_a0C_of_mAt hn hc₃η
  have hbase := integral_mgPart_sq_le (q := q) (W := W) (A₀ := A₀)
    (cstep := Submission.L10.cAdopted n) hN hA₀ hq hne hA₀m
    (DriftStopped7.etaAdopted_nonneg (n := n)) (DriftStopped7.r0Adopted_nonneg (n := n))
    hc₃0 hlt (ParamsAdopted2.numStepsAdopted2 n)
  refine le_trans hbase (le_of_eq ?_)
  have hcsq : Submission.L10.cAdopted n ^ 2 = ParamsAdopted2.stepSizeAdopted2 n := by
    rw [Submission.L10.cAdopted]
    exact Real.sq_sqrt (ParamsAdopted2.stepSizeAdopted2_nonneg hn3)
  have hNh := ParamsAdopted2.numStepsAdopted2_mul_stepSizeAdopted2 hn3
  rw [hcsq, LogDetVariance.varBound, GoodPathBounds.mAt]
  have hgroup : (ParamsAdopted2.numStepsAdopted2 n : ℝ)
      * (ParamsAdopted2.stepSizeAdopted2 n
        * ((n : ℝ) / (a0C n - (DriftStopped6.r0Adopted n
            + c₃ * DriftStopped6.etaAdopted n)) ^ 2))
      = ((ParamsAdopted2.numStepsAdopted2 n : ℝ) * ParamsAdopted2.stepSizeAdopted2 n)
        * ((n : ℝ) / (a0C n - (DriftStopped6.r0Adopted n
            + c₃ * DriftStopped6.etaAdopted n)) ^ 2) := by ring
  rw [hgroup, hNh]
  ring

end Var

end Submission.L10.LogDetMartingale

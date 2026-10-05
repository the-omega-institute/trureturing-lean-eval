import Submission.L10.TailSideSetup
import Submission.L10.WalkMeasurable

/-!
# Gate L-10 (`klartag_packing`), brief 60 — `TailSideHyp` for the chain's own data

Report 52 §4 proved the tail for **any** adapted increment family; §5 named the one thing left,
the instantiation at the chain.  This module does it.

* `measurable_of_active_vec` — the vector-valued copy of `ChainWiring.measurable_of_active`.
* `dirOf` — the chain's projected direction, **normalised by `‖q y‖`**.  The normalisation is
  forced: `TailTransport.hit_tail_yOf`'s variance identity `k·δ = t` needs the increment variance
  to be the step size `h`, and the unnormalised walk's is `h‖q y‖²`
  (`ChainWalk.hitSet_smul` is what makes the two hitting events the same).
* `tailSideHyp_of_rawData` — the target, at the scale
  **`c = √(ParamsAdopted2.stepSizeAdopted2 n)`**: the increments are `c • (standard Gaussian)`, so
  each coordinate has variance `c² = h`, which is what `PaddedLawSetup.chainRaw2_on_setup` and
  `StepInputs2.driftInputs_step_chain` (at `v = h`) expect.

## One deviation, stated up front

`RawData` does **not** determine the walk at time zero.  `hit_tail_yOf` needs
`M 0 = a₀ − (u²)⁻¹` exactly — Klartag's eq. (61) — and `RawData.hA₀` gives only `1 < ⟪A₀, q y⟫`.
`NormData` below carries the two missing identities; both are immediate for the chain's own
`q y = ChainWiring.qUT (α • toE n y)` and `A₀ = a0C n • Id`, from `ChainWiring.inner_qUT`
(`⟪qUT x, qUT x⟫ = ‖x‖⁴`) and `ChainWiring.inner_qUT_eq_quad`.  See the report, §3.
-/

set_option linter.unusedSectionVars false

namespace Submission.L10.TailSideSetup2

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal RealInnerProductSpace
open Submission.L10 Submission.L10.Increments Submission.L10.ChainSetup
open Submission.L10.PaddedLawSetup Submission.L10.TailSideSetup
open Submission.L10.Tiling Submission.L10.Section5 Submission.L10.ConstructionA

noncomputable section

/-! ## 1. The vector-valued active-set measurability lemma -/

section ActiveVec

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι] {Ω : Type*} [MeasurableSpace Ω]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
variable {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

/-- **`ChainWiring.measurable_of_active`, vector-valued.**  A statistic of the active set alone is
measurable; the proof is the same finite partition over `W.powerset`. -/
theorem measurable_of_active_vec (hξ : ∀ k, Measurable (ξ k)) (k : ℕ)
    (f : Finset ι → EuclideanSpace ℝ (UT n)) :
    Measurable fun ω => f (Chain.chain q W A₀ ξ k ω).2 := by
  classical
  have hrep : (fun ω => f (Chain.chain q W A₀ ξ k ω).2)
      = fun ω => ∑ c ∈ W.powerset, if (Chain.chain q W A₀ ξ k ω).2 = c then f c else 0 := by
    funext ω
    rw [Finset.sum_ite_eq W.powerset (Chain.chain q W A₀ ξ k ω).2 (fun c => f c),
      ite_eq_left (Finset.mem_powerset.2 (Chain.chain_snd_subset_window k ω))]
  rw [hrep]
  exact Finset.measurable_sum _ fun c _ =>
    Measurable.ite (ChainWiring.measurableSet_active_eq hξ k c) measurable_const measurable_const

end ActiveVec

/-! ## 2. The chain's past, and its normalised projected direction -/

section Direction

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}

/-- A truncated past, read back as a full path at scale `c`. -/
def extendc (c : ℝ) {i : ℕ} (z : Fin i → EuclideanSpace ℝ (UT n)) :
    ℕ → EuclideanSpace ℝ (UT n) := fun j => if h : j < i then c • z ⟨j, h⟩ else 0

theorem measurable_extendc (c : ℝ) {i : ℕ} (j : ℕ) :
    Measurable fun z : Fin i → EuclideanSpace ℝ (UT n) => extendc c z j := by
  by_cases h : j < i
  · show Measurable fun z : Fin i → EuclideanSpace ℝ (UT n) =>
      if h' : j < i then c • z ⟨j, h'⟩ else 0
    simp only [dite_eq_left h]
    exact (measurable_pi_apply _).const_smul c
  · show Measurable fun z : Fin i → EuclideanSpace ℝ (UT n) =>
      if h' : j < i then c • z ⟨j, h'⟩ else 0
    simp only [dite_eq_right h]
    exact measurable_const

theorem extendc_restr {c : ℝ} {i : ℕ} {j : ℕ} (hj : j < i)
    (ω : ℕ → EuclideanSpace ℝ (UT n)) :
    extendc c (restr i ω) j = step c j ω := by
  show (if h : j < i then c • (restr i ω) ⟨j, h⟩ else 0) = c • coord j ω
  rw [dite_eq_left hj]; rfl

/-- **The chain's projected direction at `q y`, normalised.** -/
def dirOf (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι) (A₀ : EuclideanSpace ℝ (UT n))
    (c : ℝ) (y : ι) (i : ℕ) (z : Fin i → EuclideanSpace ℝ (UT n)) :
    EuclideanSpace ℝ (UT n) :=
  ‖q y‖⁻¹ • (Chain.freeSub q (Chain.chain q W A₀
    (fun j (z' : Fin i → EuclideanSpace ℝ (UT n)) => extendc c z' j) i z).2).starProjection (q y)

theorem measurable_dirOf (c : ℝ) (y : ι) (i : ℕ) : Measurable (dirOf q W A₀ c y i) :=
  measurable_of_active_vec (ξ := fun j (z : Fin i → EuclideanSpace ℝ (UT n)) => extendc c z j)
    (fun j => measurable_extendc c j) i
    (fun a => ‖q y‖⁻¹ • (Chain.freeSub q a).starProjection (q y))

theorem norm_dirOf_le {y : ι} (hqy : q y ≠ 0) (c : ℝ) (i : ℕ)
    (z : Fin i → EuclideanSpace ℝ (UT n)) : ‖dirOf q W A₀ c y i z‖ ≤ 1 := by
  have hqn : (0 : ℝ) < ‖q y‖ := norm_pos_iff.2 hqy
  have hproj := Submodule.norm_starProjection_apply_le
    (Chain.freeSub q (Chain.chain q W A₀
      (fun j (z' : Fin i → EuclideanSpace ℝ (UT n)) => extendc c z' j) i z).2) (q y)
  rw [dirOf, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖q y‖⁻¹),
    inv_mul_le_iff₀ hqn, mul_one]
  exact hproj

/-- `Submodule.starProjection` carries a `HasOrthogonalProjection` instance argument, so `rw` on the
subspace fails; `subst` does not (report 36's `reflection_congr`, for the projection). -/
theorem starProjection_congr {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K L : Submodule ℝ E} [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (hKL : K = L) (x : E) : K.starProjection x = L.starProjection x := by subst hKL; rfl

theorem dirOf_restr (c : ℝ) (y : ι) (i : ℕ) (ω : ℕ → EuclideanSpace ℝ (UT n)) :
    dirOf q W A₀ c y i (restr i ω)
      = ‖q y‖⁻¹ • (Chain.freeSub q
          (Chain.chain q W A₀ (step c) i ω).2).starProjection (q y) := by
  have hchain : Chain.chain q W A₀
      (fun j (z : Fin i → EuclideanSpace ℝ (UT n)) => extendc c z j) i (restr i ω)
      = Chain.chain q W A₀ (step c) i ω :=
    chain_eq_of_eq (q := q) (W := W) (A₀ := A₀)
      (ξ := fun j (z : Fin i → EuclideanSpace ℝ (UT n)) => extendc c z j) (step c)
      (restr i ω) ω i (fun j hj => extendc_restr hj ω)
  show ‖q y‖⁻¹ • (Chain.freeSub q (Chain.chain q W A₀
      (fun j (z : Fin i → EuclideanSpace ℝ (UT n)) => extendc c z j) i (restr i ω)).2
      ).starProjection (q y) = _
  exact congrArg (fun v => ‖q y‖⁻¹ • v) (starProjection_congr (by rw [hchain]) (q y))

end Direction

/-! ## 3. `TailSideHyp` for the chain's own data -/

section Instantiate

/-- The two identities `RawData` does not carry: Klartag's eq. (61) at time zero.  Both are
immediate for the chain's own `q y = ChainWiring.qUT (α • toE n y)` and `A₀ = a0C n • Id`. -/
structure NormData (n : ℕ) (α : ℝ) (q : (Fin n → ℤ) → EuclideanSpace ℝ (UT n))
    (W : Finset (Fin n → ℤ)) (A₀ : EuclideanSpace ℝ (UT n)) : Prop where
  hnorm : ∀ y ∈ W, ‖q y‖ = (α * ‖toE n y‖) ^ 2
  hinner : ∀ y ∈ W, ⟪A₀, q y⟫ = a0C n * (α * ‖toE n y‖) ^ 2

theorem stepSizeAdopted2_pos {n : ℕ} (hn : 3 ≤ n) : 0 < ParamsAdopted2.stepSizeAdopted2 n := by
  have hlog : (1 : ℝ) ≤ Real.log n := ChainDrift.log_pos_of_three hn
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [ParamsAdopted2.stepSizeAdopted2, ChainDrift.stepSize, ChainDrift.horizon]
  exact div_pos (by positivity) (ChainDrift.numSteps_pos hn)

/-- **The tail-side hypothesis for the chain's own `q W A₀`, at the adopted scale.** -/
theorem tailSideHyp_of_rawData {p n : ℕ} {α R : ℝ}
    {q : (Fin n → ℤ) → EuclideanSpace ℝ (UT n)} {W : Finset (Fin n → ℤ)}
    {A₀ : EuclideanSpace ℝ (UT n)}
    (hraw : RawData p n α R q W A₀) (hnd : NormData n α q W A₀) (hn : 3 ≤ n) :
    TailSideHyp n (Real.sqrt (ParamsAdopted2.stepSizeAdopted2 n)) α q W A₀ := by
  classical
  intro k hk hk0 y hy
  set h : ℝ := ParamsAdopted2.stepSizeAdopted2 n with hh
  set c : ℝ := Real.sqrt h with hcdef
  have hh0 : 0 < h := stepSizeAdopted2_pos hn
  have hc0 : 0 < c := Real.sqrt_pos.2 hh0
  have hcsq : c ^ 2 = h := Real.sq_sqrt hh0.le
  have hqy : q y ≠ 0 := by
    intro hz
    have := hraw.hA₀ y hy
    rw [hz, inner_zero_right] at this
    linarith
  have hqn : (0 : ℝ) < ‖q y‖ := norm_pos_iff.2 hqy
  set u : ℝ := α * ‖toE n y‖ with hudef
  have hu0 : 0 < u := hraw.hr y hy
  have hqu : ‖q y‖ = u ^ 2 := hnd.hnorm y hy
  set M : ℕ → (ℕ → EuclideanSpace ℝ (UT n)) → ℝ :=
    fun i ω => ‖q y‖⁻¹ * constraintM q W A₀ (step c) y i ω with hMdef
  have hstepm : ∀ j, Measurable (step (ι := UT n) c j) := fun j => measurable_step c j
  have hMm : ∀ i, Measurable (M i) := fun i =>
    (measurable_constraintM hstepm y i).const_mul _
  have hM : ∀ i ω, M (i + 1) ω - M i ω
      = c * ⟪ω i, dirOf q W A₀ c y i (restr i ω)⟫ := by
    intro i ω
    have hps := pureWalk_succ_sub (q := q) (W := W) (A₀ := A₀) (ξ := step c) y i ω
    have hdiff : M (i + 1) ω - M i ω
        = ‖q y‖⁻¹ * (pureWalk q W A₀ (step c) y (i + 1) ω - pureWalk q W A₀ (step c) y i ω) := by
      show ‖q y‖⁻¹ * (pureWalk q W A₀ (step c) y (i + 1) ω - 1)
        - ‖q y‖⁻¹ * (pureWalk q W A₀ (step c) y i ω - 1) = _
      ring
    rw [hdiff, hps, dirOf_restr, real_inner_smul_right]
    show ‖q y‖⁻¹ * ⟪c • ω i, (Chain.freeSub q
      (Chain.chain q W A₀ (step c) i ω).2).starProjection (q y)⟫ = _
    rw [real_inner_smul_left]
    ring
  have hzero : ∀ ω, M 0 ω = a0C n - (u ^ 2)⁻¹ := by
    intro ω
    show ‖q y‖⁻¹ * (⟪A₀, q y⟫ - 1) = _
    have huu : (u : ℝ) ≠ 0 := ne_of_gt hu0
    rw [hnd.hinner y hy, hqu]
    field_simp
    ring
  have hM₀ : 0 < a0C n - (u ^ 2)⁻¹ := by
    have hgap := chain_hgap (q := q) (W := W) (A₀ := A₀) (ξ := step c) (hraw.hA₀ y hy)
      (fun _ => 0)
    have : 0 < M 0 (fun _ => 0) := mul_pos (inv_pos.2 hqn) hgap
    rwa [hzero] at this
  have ht : 0 < (k : ℝ) * h := by
    have : (0 : ℝ) < (k : ℝ) := by
      have : 0 < k := Nat.pos_of_ne_zero hk0
      exact_mod_cast this
    positivity
  have hv : ((k • Real.toNNReal (c ^ 2) : ℝ≥0) : ℝ) = (k : ℝ) * h * 1 ^ 2 := by
    rw [nsmul_eq_mul, NNReal.coe_mul, hcsq, Real.coe_toNNReal _ hh0.le]
    simp
  have hset : {ω : ℕ → EuclideanSpace ℝ (UT n) |
        ∃ i ≤ k, constraintM q W A₀ (step c) y i ω ≤ 0}
      = {ω | ∃ i ≤ k, M i ω ≤ 0} :=
    (hitSet_smul (M := constraintM q W A₀ (step c) y) (inv_pos.2 hqn) k).symm
  rw [hset]
  exact tail_of_increments hc0 (by omega) (fun i => measurable_dirOf c y i)
    (fun i z => norm_dirOf_le hqy c i z) hMm hM ht hM₀ hzero hv

end Instantiate

end

end Submission.L10.TailSideSetup2

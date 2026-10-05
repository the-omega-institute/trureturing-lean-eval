import Submission.L10.Discharge
import Submission.L10.StepGlue

/-!
# Gate L-10 (`klartag_packing`), brief 29 — the state invariant on the chain's good event

Brief 29.  `Discharge.StateInvariant` (report 25 §5, R1) is the last chain-side residual: on the
good event every state `A_k` of the chain has to satisfy `Discharge.StateBounds m M`, which is what
`Discharge.hpt_of_stateInvariant` consumes.  This module proves it.

## The route, and where it stops

`A_k = A₀ + Σ_{j<k} π_j ξ_j + Σ_{j<k} (lift correction)` (`chain_fst_eq`, pure algebra).  The three
pieces are then bounded separately:

* **the lifts** — `liftStep` vanishes off the freeze set (`liftStep_eq_zero_of_not_freezes`, from
  `Chain.freezes_iff`), so the total is at most `dim ℝ^{n×n}_sym` times the per-freeze bound,
  **not** `N` times it (`norm_liftSum_le`, from `Chain.card_freezes_le`);
* **the accumulated Gaussian part** — the Maurey split `2 π_j ξ_j = ξ_j + R_j ξ_j` with
  `R_j = Submodule.reflection (F_j)` (`starProjection_add_self`, `gaussSum_add_self`) reduces it to
  two sums of *unprojected* increments, each `N(0, k h · Id)` by the induction over `k`
  (`map_sum_scaled`) that report 6 §6 gap 2 and report 25 §5 both left open;
* **the conclusion** — `‖symMat A_k − a₀·Id‖_op ≤ ρ` with `ρ < a₀` gives `StateBounds (a₀−ρ) (a₀+ρ)`
  through `GoodEvent.lowerBound_of_opNorm_le`, `GoodEvent.posDef_of_inner_pos` and a congruence
  factor built from `CFC.sqrt` (`stateBounds_of_opNorm_le`, `exists_congr_of_posDef`).

What remains a hypothesis is named in the report: the verification that the chain's own increments
satisfy `map_sum_scaled`'s per-step independence (`IndepFun (partial sum) (next)`), which is
`Increments.indepFun_frozen_isometry` plus the filtration plumbing.
-/

namespace Submission.L10.StateInvariant

open MeasureTheory Matrix Finset Module ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace MatrixOrder
open Submission.L10 Submission.L10.Increments

noncomputable section

/-! ## Part 1. `symMat` is linear; `StateBounds` from an operator-norm bound -/

section Bounds

variable {n : ℕ}

/-! ### `symMat` is linear -/

theorem symMat_add (x y : EuclideanSpace ℝ (UT n)) :
    symMat (x + y) = symMat x + symMat y := by
  ext i j; simp [symMat_apply]; ring

theorem symMat_sub (x y : EuclideanSpace ℝ (UT n)) :
    symMat (x - y) = symMat x - symMat y := by
  ext i j; simp [symMat_apply]; ring

theorem symMat_zero : symMat (0 : EuclideanSpace ℝ (UT n)) = 0 := by
  ext i j; simp [symMat_apply]

theorem symMat_sum {α : Type*} (s : Finset α) (f : α → EuclideanSpace ℝ (UT n)) :
    symMat (∑ a ∈ s, f a) = ∑ a ∈ s, symMat (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [symMat_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, symMat_add, ih]

theorem exists_congr_of_posDef {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    ∃ S : Matrix (Fin n) (Fin n) ℝ, S.IsHermitian ∧ S * A * S = 1 := by
  have hA0 : (0 : Matrix (Fin n) (Fin n) ℝ) ≤ A := hA.posSemidef.nonneg
  set R := CFC.sqrt A with hR
  have hRR : R * R = A := CFC.sqrt_mul_sqrt_self A hA0
  have hRpsd : R.PosSemidef := (CFC.sqrt_nonneg A).posSemidef
  have hdetA : IsUnit A.det := (ne_of_gt hA.det_pos).isUnit
  have hdetR : IsUnit R.det := by
    have h : R.det * R.det = A.det := by rw [← Matrix.det_mul, hRR]
    exact isUnit_of_mul_isUnit_left (by rw [h]; exact hdetA)
  refine ⟨R⁻¹, hRpsd.isHermitian.inv, ?_⟩
  calc R⁻¹ * A * R⁻¹ = (R⁻¹ * R) * (R * R⁻¹) := by rw [← hRR]; simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [Matrix.nonsing_inv_mul R hdetR, Matrix.mul_nonsing_inv R hdetR, Matrix.one_mul]

/-- **From an operator-norm bound on `A − a₀·Id` to `StateBounds`.**  This is report 25's route:
`GoodEvent.lowerBound_of_opNorm_le` for the lower bound, the triangle inequality for the upper one,
and `CFC.sqrt` for the congruence factor. -/
theorem stateBounds_of_opNorm_le {A : Matrix (Fin n) (Fin n) ℝ} {a₀ ρ : ℝ}
    (hA : A.IsSymm) (hρ0 : 0 ≤ ρ) (hlt : ρ < a₀)
    (hG : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (A - a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))‖ ≤ ρ) :
    Discharge.StateBounds A (a₀ - ρ) (a₀ + ρ) := by
  have ha₀ : 0 < a₀ := lt_of_le_of_lt hρ0 hlt
  have hsplit : a₀ • (1 : Matrix (Fin n) (Fin n) ℝ)
      + (A - a₀ • (1 : Matrix (Fin n) (Fin n) ℝ)) = A := by abel
  have hlower : ∀ x : EuclideanSpace ℝ (Fin n),
      (a₀ - ρ) * ‖x‖ ^ 2 ≤ ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) A x⟫ := by
    intro x
    have h := GoodEvent.lowerBound_of_opNorm_le (a₀ := a₀) hG x
    rwa [hsplit] at h
  have hmpos : 0 < a₀ - ρ := by linarith
  have hpd : A.PosDef := by
    refine GoodEvent.posDef_of_inner_pos (Matrix.isHermitian_iff_isSymm.2 hA) fun x hx => ?_
    have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hl := hlower x
    linarith [hl, mul_pos hmpos (pow_pos hx0 2)]
  refine ⟨hpd, hmpos, hlower, by linarith, ?_, exists_congr_of_posDef hpd⟩
  have hid : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))‖ ≤ a₀ := by
    rw [map_smul, map_one, norm_smul, Real.norm_eq_abs, abs_of_pos ha₀]
    calc a₀ * ‖(1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))‖
        ≤ a₀ * 1 := by
          exact mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le ha₀.le
      _ = a₀ := mul_one a₀
  calc ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖
      = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
          + Matrix.toEuclideanCLM (𝕜 := ℝ) (A - a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))‖ := by
        rw [← map_add, hsplit]
    _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))‖
          + ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (A - a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))‖ :=
        norm_add_le _ _
    _ ≤ a₀ + ρ := add_le_add hid hG

end Bounds

/-! ## Part 2. The decomposition of `A_k`, and the lift accounting -/

section Decomposition

variable {n : ℕ} {ι : Type*} [DecidableEq ι] {Ω : Type*}
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

/-- The projected Gaussian part of one step. -/
noncomputable def gaussStep (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι)
    (A₀ : EuclideanSpace ℝ (UT n)) (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (k : ℕ) (ω : Ω) :
    EuclideanSpace ℝ (UT n) :=
  (Chain.freeSub q (Chain.chain q W A₀ ξ k ω).2).starProjection (ξ k ω)

/-- The one-sided lift applied at one step. -/
noncomputable def liftStep (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι)
    (A₀ : EuclideanSpace ℝ (UT n)) (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (k : ℕ) (ω : Ω) :
    EuclideanSpace ℝ (UT n) :=
  (Chain.chain q W A₀ ξ (k + 1) ω).1 - ChainWiring.preState q W A₀ ξ k ω

noncomputable def gaussSum (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι)
    (A₀ : EuclideanSpace ℝ (UT n)) (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (k : ℕ) (ω : Ω) :
    EuclideanSpace ℝ (UT n) :=
  ∑ j ∈ Finset.range k, gaussStep q W A₀ ξ j ω

noncomputable def liftSum (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι)
    (A₀ : EuclideanSpace ℝ (UT n)) (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (k : ℕ) (ω : Ω) :
    EuclideanSpace ℝ (UT n) :=
  ∑ j ∈ Finset.range k, liftStep q W A₀ ξ j ω

theorem preState_eq (k : ℕ) (ω : Ω) :
    ChainWiring.preState q W A₀ ξ k ω
      = (Chain.chain q W A₀ ξ k ω).1 + gaussStep q W A₀ ξ k ω := rfl

/-- **The decomposition.**  `A_k = A₀ + (accumulated projected Gaussian) + (accumulated lifts)`. -/
theorem chain_fst_eq (k : ℕ) (ω : Ω) :
    (Chain.chain q W A₀ ξ k ω).1
      = A₀ + gaussSum q W A₀ ξ k ω + liftSum q W A₀ ξ k ω := by
  induction k with
  | zero => simp [gaussSum, liftSum]
  | succ k ih =>
    have h : (Chain.chain q W A₀ ξ (k + 1) ω).1
        = ChainWiring.preState q W A₀ ξ k ω + liftStep q W A₀ ξ k ω := by
      rw [liftStep]; abel
    rw [h, preState_eq, ih]
    simp only [gaussSum, liftSum, Finset.sum_range_succ]
    abel

/-- Off the freeze set the lift is the identity. -/
theorem liftStep_eq_zero_of_not_freezes (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    {k : ℕ} {ω : Ω} (hfz : ¬ Chain.Freezes q W A₀ ξ k ω) :
    liftStep q W A₀ ξ k ω = 0 := by
  have h := (Chain.freezes_iff hA₀ hq hne k ω).not.1 hfz
  rw [Finset.not_nonempty_iff_eq_empty] at h
  have hfix : (Chain.chain q W A₀ ξ (k + 1) ω).1 = ChainWiring.preState q W A₀ ξ k ω :=
    ChainWiring.lift_eq_self_of_violated_empty q W _ h
  rw [liftStep, hfix, sub_self]

/-- **The lift accounting.**  The corrections are paid at most `dim ℝ^{n×n}_sym` times, not `N`
times — `Chain.card_freezes_le`. -/
theorem norm_liftSum_le (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    {ε : ℝ} (hε0 : 0 ≤ ε) (k : ℕ) (ω : Ω)
    (hb : ∀ j, j < k → ‖liftStep q W A₀ ξ j ω‖ ≤ ε) :
    ‖liftSum q W A₀ ξ k ω‖
      ≤ (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) * ε := by
  classical
  have hzero : ∀ j ∈ (Finset.range k).filter
      (fun j => ¬ Chain.Freezes q W A₀ ξ j ω), ‖liftStep q W A₀ ξ j ω‖ = 0 := by
    intro j hj
    rw [liftStep_eq_zero_of_not_freezes hA₀ hq hne (Finset.mem_filter.1 hj).2, norm_zero]
  have hsplit : ∑ j ∈ Finset.range k, ‖liftStep q W A₀ ξ j ω‖
      = ∑ j ∈ (Finset.range k).filter (fun j => Chain.Freezes q W A₀ ξ j ω),
          ‖liftStep q W A₀ ξ j ω‖ := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range k)
      (fun j => Chain.Freezes q W A₀ ξ j ω), Finset.sum_eq_zero hzero, add_zero]
  have hcard : (((Finset.range k).filter fun j => Chain.Freezes q W A₀ ξ j ω).card : ℝ)
      ≤ (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) := by
    have h := Chain.card_freezes_le (ξ := ξ) hA₀ hq hne k ω
    exact_mod_cast le_trans (Nat.le_add_right _ _) h
  calc ‖liftSum q W A₀ ξ k ω‖
      ≤ ∑ j ∈ Finset.range k, ‖liftStep q W A₀ ξ j ω‖ := norm_sum_le _ _
    _ = ∑ j ∈ (Finset.range k).filter (fun j => Chain.Freezes q W A₀ ξ j ω),
          ‖liftStep q W A₀ ξ j ω‖ := hsplit
    _ ≤ (((Finset.range k).filter fun j => Chain.Freezes q W A₀ ξ j ω).card : ℝ) * ε := by
        rw [← nsmul_eq_mul]
        refine Finset.sum_le_card_nsmul _ _ _ fun j hj => ?_
        exact hb j (Finset.mem_range.1 (Finset.mem_filter.1 hj).1)
    _ ≤ (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) * ε :=
        mul_le_mul_of_nonneg_right hcard hε0

end Decomposition

/-! ## Part 3. The scaled Gaussian on `E`, and the Maurey induction over `k` -/

section Maurey

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- `N(0, c²·Id)` on `E`: the standard Gaussian scaled by `c`. -/
def scaled (c : ℝ) (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] : Measure E :=
  (stdGaussian E).map (c • ·)

instance (c : ℝ) : IsProbabilityMeasure (scaled c E) := by
  unfold scaled
  infer_instance

theorem charFun_scaled (c : ℝ) (t : E) :
    charFun (scaled c E) t = Complex.exp (-(c ^ 2 * ‖t‖ ^ 2) / 2) := by
  rw [scaled, charFun_map_smul, charFun_stdGaussian]
  congr 1
  have h : ‖c • t‖ ^ 2 = c ^ 2 * ‖t‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hc : ((‖c • t‖ : ℝ) : ℂ) ^ 2 = ((c ^ 2 * ‖t‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, h]
  rw [hc]
  push_cast
  ring

/-- **The convolution identity**: `N(0,a²) ∗ N(0,b²) = N(0,a²+b²)` on `E`. -/
theorem scaled_conv_scaled {a b : ℝ} (_ha : 0 ≤ a) (_hb : 0 ≤ b) :
    (scaled a E) ∗ (scaled b E) = scaled (Real.sqrt (a ^ 2 + b ^ 2)) E := by
  refine Measure.ext_of_charFun ?_
  funext t
  rw [charFun_conv, charFun_scaled, charFun_scaled, charFun_scaled, ← Complex.exp_add]
  congr 1
  have h : (Real.sqrt (a ^ 2 + b ^ 2)) ^ 2 = a ^ 2 + b ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hc : ((Real.sqrt (a ^ 2 + b ^ 2) : ℝ) : ℂ) ^ 2 = ((a ^ 2 + b ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, h]
  rw [hc]
  push_cast
  ring

end Maurey

section MaureyInd

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The Maurey induction over `k`** (report 6 §6 gap 2): a sum of `k` increments, each
`N(0, c²·Id)` and each independent of the partial sum before it, is `N(0, k c²·Id)`. -/
theorem map_sum_scaled {X : ℕ → Ω → E} {c : ℝ} (hc : 0 ≤ c)
    (hmeas : ∀ j, Measurable (X j))
    (hlaw : ∀ j, P.map (X j) = scaled c E)
    (hind : ∀ k, IndepFun (fun ω => ∑ j ∈ Finset.range k, X j ω) (X k) P) (k : ℕ) :
    P.map (fun ω => ∑ j ∈ Finset.range k, X j ω) = scaled (Real.sqrt k * c) E := by
  induction k with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, Real.sqrt_zero, zero_mul]
    rw [Measure.map_const]
    simp [scaled, Measure.map_const]
  | succ k ih =>
    have hSm : Measurable fun ω => ∑ j ∈ Finset.range k, X j ω :=
      Finset.measurable_sum _ fun j _ => hmeas j
    have hsplit : (fun ω => ∑ j ∈ Finset.range (k + 1), X j ω)
        = (fun ω => ∑ j ∈ Finset.range k, X j ω) + X k := by
      funext ω; simp [Finset.sum_range_succ]
    rw [hsplit, (hind k).map_add_eq_map_conv_map₀ hSm.aemeasurable (hmeas k).aemeasurable,
      ih, hlaw k, scaled_conv_scaled (by positivity) hc]
    congr 1
    have h : (Real.sqrt k * c) ^ 2 + c ^ 2 = ((k : ℝ) + 1) * c ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg k)]
      ring
    rw [h, Real.sqrt_mul (by positivity), Real.sqrt_sq hc]
    push_cast
    ring

end MaureyInd

/-! ## Part 4. The Maurey split of the accumulated projected sum -/

section Split

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `π x + π x = x + R x` with `R = Submodule.reflection K`: the Maurey split at one step. -/
theorem starProjection_add_self (K : Submodule ℝ E) [K.HasOrthogonalProjection] (x : E) :
    K.starProjection x + K.starProjection x = x + K.reflection x := by
  rw [Submodule.reflection_apply, two_smul]
  abel

end Split

section SplitChain

variable {n : ℕ} {ι : Type*} [DecidableEq ι] {Ω : Type*}
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

/-- The reflected increment `R_j ξ_j`, `R_j = π_j − π̃_j`. -/
noncomputable def reflStep (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι)
    (A₀ : EuclideanSpace ℝ (UT n)) (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (k : ℕ) (ω : Ω) :
    EuclideanSpace ℝ (UT n) :=
  (Chain.freeSub q (Chain.chain q W A₀ ξ k ω).2).reflection (ξ k ω)

/-- **The Maurey split, accumulated**: `2 Σ_{j<k} π_j ξ_j = Σ_{j<k} ξ_j + Σ_{j<k} R_j ξ_j`.
Both sums on the right are over *unprojected* increments, which is what makes the induction
possible. -/
theorem gaussSum_add_self (k : ℕ) (ω : Ω) :
    gaussSum q W A₀ ξ k ω + gaussSum q W A₀ ξ k ω
      = (∑ j ∈ Finset.range k, ξ j ω) + ∑ j ∈ Finset.range k, reflStep q W A₀ ξ j ω := by
  rw [gaussSum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => starProjection_add_self _ _

/-- Hence the accumulated projected sum is dominated by the two halves. -/
theorem opNorm_gaussSum_le (k : ℕ) (ω : Ω) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat (gaussSum q W A₀ ξ k ω))‖
      ≤ (‖Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat (∑ j ∈ Finset.range k, ξ j ω))‖
          + ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
              (symMat (∑ j ∈ Finset.range k, reflStep q W A₀ ξ j ω))‖) / 2 := by
  have h := gaussSum_add_self (q := q) (W := W) (A₀ := A₀) (ξ := ξ) k ω
  have h2 : Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat (gaussSum q W A₀ ξ k ω))
      + Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat (gaussSum q W A₀ ξ k ω))
      = Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat (∑ j ∈ Finset.range k, ξ j ω))
        + Matrix.toEuclideanCLM (𝕜 := ℝ)
            (symMat (∑ j ∈ Finset.range k, reflStep q W A₀ ξ j ω)) := by
    rw [← map_add, ← map_add, ← symMat_add, ← symMat_add, h]
  have h3 := norm_add_le
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat (∑ j ∈ Finset.range k, ξ j ω)))
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat (∑ j ∈ Finset.range k, reflStep q W A₀ ξ j ω)))
  have h4 : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat (gaussSum q W A₀ ξ k ω))
      + Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat (gaussSum q W A₀ ξ k ω))‖
      = 2 * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat (gaussSum q W A₀ ξ k ω))‖ := by
    rw [← two_smul ℝ, norm_smul, Real.norm_eq_abs]
    norm_num
  rw [h2] at h4
  linarith

end SplitChain

/-! ## Part 5. Corollary 3.2 for a scaled Gaussian, and the accumulated event -/

section Tail

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem symMat_smul (c : ℝ) (x : EuclideanSpace ℝ (UT n)) :
    symMat (c • x) = c • symMat x := by
  ext i j
  simp only [symMat_apply, Matrix.smul_apply, smul_eq_mul, PiLp.smul_apply]
  ring

theorem measurable_opNorm_symMat :
    Measurable fun x : EuclideanSpace ℝ (UT n) =>
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat x)‖ := by
  have h : ∀ x : EuclideanSpace ℝ (UT n), symMat x = mkMat (coordVec 1 x) := by
    intro x
    rw [← smul_symMat_eq_mkMat, one_smul]
  simp only [h]
  exact measurable_opNorm_mkMat.comp (measurable_coordVec 1)

omit [IsProbabilityMeasure P] in
/-- **Corollary 3.2 for a scaled standard Gaussian on the `UT n` carrier.**  If `Z` has law
`N(0, ρ²·Id)` then its symmetric matrix obeys Klartag's operator-norm tail. -/
theorem measureReal_opNorm_symMat_ge {Z : Ω → EuclideanSpace ℝ (UT n)} {ρ : ℝ} (hρ : 0 < ρ)
    (hZ : Measurable Z) (hlaw : P.map Z = scaled ρ (EuclideanSpace ℝ (UT n)))
    (s : ℝ) (hs : 1 ≤ s) :
    P.real {ω | 6 * ρ * s * Real.sqrt n ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat (Z ω))‖}
      ≤ 4 * Real.exp (-(s ^ 2 * n)) := by
  set thr : ℝ := 6 * ρ * s * Real.sqrt n with hthr
  set S : Set (EuclideanSpace ℝ (UT n)) :=
    {z | thr ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat z)‖} with hS
  have hSmeas : MeasurableSet S :=
    measurableSet_le measurable_const measurable_opNorm_symMat
  rw [show {ω | thr ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat (Z ω))‖} = Z ⁻¹' S from rfl,
    measureReal_preimage P hZ hSmeas, hlaw, scaled,
    ← measureReal_preimage (stdGaussian (EuclideanSpace ℝ (UT n)))
      (by fun_prop : Measurable fun x : EuclideanSpace ℝ (UT n) => ρ • x) hSmeas]
  have hset : (fun x : EuclideanSpace ℝ (UT n) => ρ • x) ⁻¹' S
      = {x : EuclideanSpace ℝ (UT n) | thr ≤
          ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (ρ • symMat x)‖} := by
    ext x
    simp only [Set.mem_preimage, hS, Set.mem_ofPred_eq, symMat_smul]
  rw [hset]
  exact increment_opNorm_tail hρ measurable_id (Measure.map_id) s hs

end Tail

section AccGood

variable {n : ℕ} {ι : Type*} [DecidableEq ι] {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

/-- **The accumulated Gaussian event**: every partial sum `Σ_{j<k} π_j ξ_j`, `k < N`, has small
operator norm.  `Discharge.chainGood`'s `goodEvent` controls *one* matrix; the invariant needs all
`N` partial sums, which is the union bound report 25 §5 prices at `4 N e^{−n}`. -/
def accGood (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι) (A₀ : EuclideanSpace ℝ (UT n))
    (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (N : ℕ) (r₀ : ℝ) : Set Ω :=
  {ω | ∀ k, k < N →
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat (gaussSum q W A₀ ξ k ω))‖ ≤ r₀}

/-- **The failure probability of the accumulated event**, from the Maurey split and the two
halves' laws: `2 N` applications of Corollary 3.2. -/
theorem measureReal_compl_accGood_le {N : ℕ} {r₀ s : ℝ} {ρ : ℕ → ℝ}
    (hρ : ∀ k, 0 < ρ k) (hs : 1 ≤ s)
    (hξm : ∀ k, Measurable (ξ k))
    (hrm : ∀ k, Measurable (reflStep q W A₀ ξ k))
    (hξlaw : ∀ k, P.map (fun ω => ∑ j ∈ Finset.range k, ξ j ω)
      = scaled (ρ k) (EuclideanSpace ℝ (UT n)))
    (hrlaw : ∀ k, P.map (fun ω => ∑ j ∈ Finset.range k, reflStep q W A₀ ξ j ω)
      = scaled (ρ k) (EuclideanSpace ℝ (UT n)))
    (hthr : ∀ k, k < N → 6 * ρ k * s * Real.sqrt n ≤ r₀) :
    P.real (accGood q W A₀ ξ N r₀)ᶜ
      ≤ (N : ℝ) * (2 * (4 * Real.exp (-(s ^ 2 * n)))) := by
  classical
  set c : ℝ := 4 * Real.exp (-(s ^ 2 * n)) with hc
  have hsub : (accGood q W A₀ ξ N r₀)ᶜ ⊆ ⋃ k ∈ Finset.range N,
      ({ω | 6 * ρ k * s * Real.sqrt n ≤
          ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat (∑ j ∈ Finset.range k, ξ j ω))‖}
        ∪ {ω | 6 * ρ k * s * Real.sqrt n ≤
          ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
            (symMat (∑ j ∈ Finset.range k, reflStep q W A₀ ξ j ω))‖}) := by
    intro ω hω
    simp only [accGood, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_le] at hω
    obtain ⟨k, hk, hlt⟩ := hω
    refine Set.mem_biUnion (Finset.mem_range.2 hk) ?_
    by_contra hcon
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hcon
    have hb := opNorm_gaussSum_le (q := q) (W := W) (A₀ := A₀) (ξ := ξ) k ω
    have h1 := hthr k hk
    linarith [hcon.1, hcon.2, hb, hlt]
  calc P.real (accGood q W A₀ ξ N r₀)ᶜ
      ≤ P.real (⋃ k ∈ Finset.range N, _) := measureReal_mono hsub (measure_ne_top P _)
    _ ≤ ∑ k ∈ Finset.range N, P.real
          ({ω | 6 * ρ k * s * Real.sqrt n ≤
            ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat (∑ j ∈ Finset.range k, ξ j ω))‖}
          ∪ {ω | 6 * ρ k * s * Real.sqrt n ≤
            ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
              (symMat (∑ j ∈ Finset.range k, reflStep q W A₀ ξ j ω))‖}) :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _k ∈ Finset.range N, (2 * c) := by
        refine Finset.sum_le_sum fun k _ => ?_
        refine (measureReal_union_le _ _).trans ?_
        have hA := measureReal_opNorm_symMat_ge (hρ k)
          (Finset.measurable_sum _ fun j _ => hξm j) (hξlaw k) s hs
        have hB := measureReal_opNorm_symMat_ge (hρ k)
          (Finset.measurable_sum _ fun j _ => hrm j) (hrlaw k) s hs
        linarith
    _ = (N : ℝ) * (2 * c) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end AccGood

/-! ## Part 6. The invariant -/

section Invariant

variable {n : ℕ} {ι : Type*} [DecidableEq ι] {Ω : Type*} [MeasurableSpace Ω]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

omit [MeasurableSpace Ω] in
/-- **R1 of report 25.**  On the chain's good event every state satisfies `StateBounds`. -/
theorem stateInvariant_of_chainGood
    {G : Ω → Matrix (Fin n) (Fin n) ℝ} {r : ℝ} {N : ℕ} {η a₀ r₀ ε : ℝ}
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hε0 : 0 ≤ ε) (hr₀ : 0 ≤ r₀)
    (hacc : ∀ k, k < N → ∀ ω ∈ Discharge.chainGood G r ξ N η,
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat (gaussSum q W A₀ ξ k ω))‖ ≤ r₀)
    (hlift : ∀ k, k < N → ∀ ω ∈ Discharge.chainGood G r ξ N η, ∀ j, j < k →
      ‖liftStep q W A₀ ξ j ω‖ ≤ ε)
    (hlt : r₀ + (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) * ε < a₀) :
    Discharge.StateInvariant q W A₀ ξ G r N η
      (a₀ - (r₀ + (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) * ε))
      (a₀ + (r₀ + (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) * ε)) := by
  intro k hk ω hω
  have hd0 : (0 : ℝ) ≤ (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) := Nat.cast_nonneg _
  have hρ0 : (0 : ℝ) ≤ r₀ + (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) * ε :=
    add_nonneg hr₀ (mul_nonneg hd0 hε0)
  refine stateBounds_of_opNorm_le (symMat_isSymm _) hρ0 hlt ?_
  have hdec : symMat (Chain.chain q W A₀ ξ k ω).1
      - a₀ • (1 : Matrix (Fin n) (Fin n) ℝ)
      = symMat (gaussSum q W A₀ ξ k ω) + symMat (liftSum q W A₀ ξ k ω) := by
    rw [chain_fst_eq, symMat_add, symMat_add, hA₀m]
    abel
  rw [hdec, map_add]
  refine (norm_add_le _ _).trans (add_le_add (hacc k hk ω hω) ?_)
  exact (StepInputs2.opNorm_symMat_le_norm _).trans
    (norm_liftSum_le hA₀ hq hne hε0 k ω (hlift k hk ω hω))

omit [MeasurableSpace Ω] in
/-- **R1 in the form the discharge successor consumes**: the accumulated event `accGood` supplies
`hacc`, so the only remaining input is the per-freeze lift bound. -/
theorem stateInvariant_of_accGood
    {G : Ω → Matrix (Fin n) (Fin n) ℝ} {r : ℝ} {N : ℕ} {η a₀ r₀ ε : ℝ}
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hε0 : 0 ≤ ε) (hr₀ : 0 ≤ r₀)
    (hsub : Discharge.chainGood G r ξ N η ⊆ accGood q W A₀ ξ N r₀)
    (hlift : ∀ k, k < N → ∀ ω ∈ Discharge.chainGood G r ξ N η, ∀ j, j < k →
      ‖liftStep q W A₀ ξ j ω‖ ≤ ε)
    (hlt : r₀ + (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) * ε < a₀) :
    Discharge.StateInvariant q W A₀ ξ G r N η
      (a₀ - (r₀ + (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) * ε))
      (a₀ + (r₀ + (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) * ε)) :=
  stateInvariant_of_chainGood hA₀ hq hne hA₀m hε0 hr₀
    (fun k hk _ hω => hsub hω k hk) hlift hlt

end Invariant

end

end Submission.L10.StateInvariant

import Submission.L10.Assembly
import Submission.L10.Final
import Submission.L10.StepInputs2

/-!
# Gate L-10 (`klartag_packing`) — discharging `Remaining.large`

Brief 25.  `Final.Remaining.large` is the last hypothesis of `Final.klartag_packing_of_hyps`
(report 17).  This module does the parts of its discharge that do not wait on another brief:

1. **The Frobenius bridge** `matToUT` — the inverse of `Increments.symMat` on symmetric matrices,
   which is what turns the one-step inequality's trace term `tr(A⁻¹ H)` into the inner product
   `⟪V, ξ⟫` that `StepInputs2.driftInputs_step_chain` consumes.
2. **The chain's good event** `chainGood = goodEvent ∩ stepGood`, its failure probability, and the
   numbers at the adopted step size: `η ≤ √2 · n⁻²`, union-bound cost `≤ 33 n⁷ log n · e^{−n}`,
   total failure `≤ 33 n⁷ log n · e^{−n} + 4 e^{−n}`, which is below `1` from `n = 28` and
   `o(1)` thereafter.
3. **The head-room check**: the good event costs the existence step `q·(M' − m₀)` of head-room, so
   `exists_mem_le_of_integral_le` applies as soon as that is below the slack — and `c₀ = e^{−C'/2}`
   is positive regardless, since the good event shifts the *threshold*, not the constant's sign.
4. **`hpt` at the chain**: the pointwise one-step bound of `driftInputs_step_chain`, assembled from
   `ChainWiring.logDet_chain_succ`, `StepInputs2.log_det_step_unconj` and
   `StepInputs2.opNorm_step_le_of_stepGood`, **given** the state bounds `StateBounds` on `A_k`.

What is *not* here, and why, is §5: `StateBounds` at the chain is not proved, because it needs the
Maurey induction over `k` that report 6 §6 gap 2 left to the chain module and that no brief has
written.  Stating it as a hypothesis with an exact signature is what rule 12 asks for.
-/

set_option linter.unusedSectionVars false

namespace Submission.L10.Discharge

open MeasureTheory Matrix Metric Finset Module ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace
open Submission.L10 Submission.L10.Increments

/-! ## 1. The Frobenius bridge: `symMat`'s inverse on symmetric matrices -/

variable {n : ℕ}

/-- The coordinate vector of a symmetric matrix — the inverse of `Increments.symMat`. -/
noncomputable def matToUT (M : Matrix (Fin n) (Fin n) ℝ) : EuclideanSpace ℝ (UT n) :=
  WithLp.toLp 2 fun p => M p.1.1 p.1.2 / cc p

@[simp] theorem matToUT_apply (M : Matrix (Fin n) (Fin n) ℝ) (p : UT n) :
    (matToUT M) p = M p.1.1 p.1.2 / cc p := rfl

theorem symMat_matToUT {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsSymm) (i j : Fin n) :
    symMat (matToUT M) i j = M i j := by
  rw [symMat_apply, matToUT_apply, mul_comm, div_mul_cancel₀ _ (ChainWiring.cc_ne_zero _)]
  rcases le_total i j with h | h
  · rw [up_of_le h]
  · rw [up_comm, up_of_le h]
    exact hM.apply i j

/-- `tr(B H) = ∑_{i,j} B_ij H_ij` for symmetric `H`: the trace term of the one-step inequality is
a Frobenius inner product. -/
theorem trace_mul_eq_frobenius {B H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsSymm) :
    (B * H).trace = ∑ i, ∑ j, B i j * H i j := by
  rw [Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hH.apply i j]

/-- **The trace term as an inner product.**  With `H = symMat u` the step's increment and `B` a
symmetric matrix, `tr(B H) = ⟪matToUT B, u⟫` — the form `driftInputs_step_chain`'s `V` takes. -/
theorem trace_mul_symMat_eq_inner {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsSymm)
    (u : EuclideanSpace ℝ (UT n)) : (B * symMat u).trace = ⟪matToUT B, u⟫ := by
  rw [trace_mul_eq_frobenius (symMat_isSymm u), ← sum_symMat_mul_eq_inner (matToUT B) u]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    rw [symMat_matToUT hB]

/-! ## 2. The chain's good event, and the numbers -/

section GoodEventChain

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The chain's good event**: the accumulated Gaussian part is controlled (Klartag's
Proposition 3.4, p. 16 eq. 43) *and* every single step is (report 15's `stepGood`, which
`GoodEvent.oneStep_of_good` needs and which the accumulated bound does not imply). -/
def chainGood (G : Ω → Matrix (Fin n) (Fin n) ℝ) (r : ℝ)
    (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (N : ℕ) (η : ℝ) : Set Ω :=
  GoodEvent.goodEvent G r ∩ StepInputs2.stepGood ξ N η

theorem mem_chainGood {G : Ω → Matrix (Fin n) (Fin n) ℝ} {r : ℝ}
    {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)} {N : ℕ} {η : ℝ} {ω : Ω} :
    ω ∈ chainGood G r ξ N η ↔
      ω ∈ GoodEvent.goodEvent G r ∧ ω ∈ StepInputs2.stepGood ξ N η := Iff.rfl

/-- The two failure probabilities add. -/
theorem measureReal_compl_chainGood_le (G : Ω → Matrix (Fin n) (Fin n) ℝ) (r : ℝ)
    (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (N : ℕ) (η : ℝ) :
    P.real (chainGood G r ξ N η)ᶜ
      ≤ P.real (GoodEvent.goodEvent G r)ᶜ + P.real (StepInputs2.stepGood ξ N η)ᶜ := by
  have hset : (chainGood G r ξ N η)ᶜ
      = (GoodEvent.goodEvent G r)ᶜ ∪ (StepInputs2.stepGood ξ N η)ᶜ := by
    rw [chainGood, Set.compl_inter]
  rw [hset]
  exact measureReal_union_le _ _

/-- **The chain's failure probability**, both halves at the chain's scale. -/
theorem measureReal_compl_chainGood_chainScale (B : Ω → Matrix (Fin n) (Fin n) ℝ)
    {T : ℝ} (hT : 0 ≤ T) (v w : ℝ≥0) (hv : (v : ℝ) = T / 4) (hvpos : 0 < v) (hn : 0 < n)
    (hindep : iIndepFun (fun (p : Fin n × Fin n) (ω : Ω) => B ω p.1 p.2) P)
    (hlawB : ∀ i j, P.map (fun ω => B ω i j) = gaussianReal 0 v)
    {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)} (hwpos : 0 < w)
    (hlawξ : ∀ k, ∀ p : UT n, P.map (fun ω => ξ k ω p) = gaussianReal 0 w) (N : ℕ) :
    P.real (chainGood (fun ω => B ω + (B ω)ᵀ) (6 * Real.sqrt (T * n)) ξ N
        (Real.sqrt (2 * (w : ℝ) * (Fintype.card (UT n) : ℝ) * (n : ℝ))))ᶜ
      ≤ 4 * Real.exp (-(n : ℝ))
        + (N : ℝ) * ((Fintype.card (UT n) : ℝ) * (2 * Real.exp (-(n : ℝ)))) := by
  refine le_trans (measureReal_compl_chainGood_le _ _ _ _ _) (add_le_add ?_ ?_)
  · exact GoodEvent.measureReal_compl_goodEvent_chainScale P B hT v hv hvpos hindep hlawB
  · exact StepInputs2.measureReal_compl_stepGood_chainScale hwpos hn hlawξ N

end GoodEventChain

/-! ### The numbers at the adopted step size -/

theorem card_UT_le_sq {n : ℕ} (hn : 1 ≤ n) : (Fintype.card (UT n) : ℝ) ≤ (n : ℝ) ^ 2 := by
  have hnat : Fintype.card (UT n) ≤ n * n := by
    rw [ChainWiring.card_UT]
    refine Nat.div_le_of_le_mul ?_
    have : n + 1 ≤ 2 * n := by omega
    calc n * (n + 1) ≤ n * (2 * n) := Nat.mul_le_mul_left _ this
      _ = 2 * (n * n) := by ring
  have := (Nat.cast_le (α := ℝ)).2 hnat
  calc (Fintype.card (UT n) : ℝ) ≤ ((n * n : ℕ) : ℝ) := this
    _ = (n : ℝ) ^ 2 := by push_cast; ring

/-- **`η ≤ √2 · n⁻²`.**  The per-step threshold `√(2 h d n)` at `h = stepSizeAdopted n ≤ n⁻⁷` and
`d = dim ℝ^{n×n}_sym ≤ n²`. -/
theorem eta_le {n : ℕ} (hn : 3 ≤ n) :
    Real.sqrt (2 * ChainWiring.stepSizeAdopted n * (Fintype.card (UT n) : ℝ) * (n : ℝ))
      ≤ Real.sqrt 2 / (n : ℝ) ^ 2 := by
  have hn1 : (1 : ℕ) ≤ n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by
    have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hstep0 : 0 ≤ ChainWiring.stepSizeAdopted n := by
    rw [ChainWiring.stepSizeAdopted, ChainDrift.stepSize, ChainDrift.horizon]
    have : (0 : ℝ) ≤ Real.log n :=
      le_trans (by norm_num) (ChainDrift.log_pos_of_three hn)
    positivity
  have hd := card_UT_le_sq hn1
  have hd0 : (0 : ℝ) ≤ (Fintype.card (UT n) : ℝ) := Nat.cast_nonneg _
  have hh := ChainWiring.stepSizeAdopted_le hn
  have hbound : 2 * ChainWiring.stepSizeAdopted n * (Fintype.card (UT n) : ℝ) * (n : ℝ)
      ≤ 2 / (n : ℝ) ^ 4 := by
    have h1 : 2 * ChainWiring.stepSizeAdopted n * (Fintype.card (UT n) : ℝ) * (n : ℝ)
        ≤ 2 * (1 / (n : ℝ) ^ 7) * (n : ℝ) ^ 2 * (n : ℝ) := by
      have hA : ChainWiring.stepSizeAdopted n * (Fintype.card (UT n) : ℝ)
          ≤ (1 / (n : ℝ) ^ 7) * (n : ℝ) ^ 2 :=
        mul_le_mul hh hd hd0 (by positivity)
      nlinarith [hA, hnR]
    calc 2 * ChainWiring.stepSizeAdopted n * (Fintype.card (UT n) : ℝ) * (n : ℝ)
        ≤ 2 * (1 / (n : ℝ) ^ 7) * (n : ℝ) ^ 2 * (n : ℝ) := h1
      _ = 2 / (n : ℝ) ^ 4 := by field_simp
  calc Real.sqrt (2 * ChainWiring.stepSizeAdopted n * (Fintype.card (UT n) : ℝ) * (n : ℝ))
      ≤ Real.sqrt (2 / (n : ℝ) ^ 4) := Real.sqrt_le_sqrt hbound
    _ = Real.sqrt 2 / (n : ℝ) ^ 2 := by
        rw [Real.sqrt_div' 2 (by positivity), show ((n : ℝ) ^ 4) = ((n : ℝ) ^ 2) ^ 2 by ring,
          Real.sqrt_sq (by positivity)]

/-- **The union-bound cost `≤ 33 n⁷ log n`.**  Report 25's brief quotes `32 n⁷ log n`, which is the
leading term; the ceiling in `N = ⌈16 n⁵ log n⌉` adds `2n²`, and `2n² ≤ n⁷ log n` for `n ≥ 3`. -/
theorem stepGood_cost_le {n : ℕ} (hn : 3 ≤ n) :
    ((ChainWiring.numStepsAdopted n : ℕ) : ℝ) * ((Fintype.card (UT n) : ℝ) * 2)
      ≤ 33 * (n : ℝ) ^ 7 * Real.log n := by
  have hn1 : (1 : ℕ) ≤ n := by omega
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog1 : (1 : ℝ) ≤ Real.log n := ChainDrift.log_pos_of_three hn
  have hN : ((ChainWiring.numStepsAdopted n : ℕ) : ℝ) ≤ 16 * (n : ℝ) ^ 5 * Real.log n + 1 :=
    le_of_lt (Nat.ceil_lt_add_one (by positivity))
  have hd := card_UT_le_sq hn1
  have hd0 : (0 : ℝ) ≤ (Fintype.card (UT n) : ℝ) := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ ((ChainWiring.numStepsAdopted n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hstep : ((ChainWiring.numStepsAdopted n : ℕ) : ℝ) * ((Fintype.card (UT n) : ℝ) * 2)
      ≤ (16 * (n : ℝ) ^ 5 * Real.log n + 1) * ((n : ℝ) ^ 2 * 2) := by
    have h1 : (Fintype.card (UT n) : ℝ) * 2 ≤ (n : ℝ) ^ 2 * 2 := by linarith
    have hc0 : (0 : ℝ) ≤ (Fintype.card (UT n) : ℝ) * 2 := by positivity
    have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
    have hpow : (0 : ℝ) ≤ (n : ℝ) ^ 5 := by positivity
    have hb0 : (0 : ℝ) ≤ 16 * (n : ℝ) ^ 5 * Real.log n + 1 := by nlinarith [hlog1, hpow]
    exact mul_le_mul hN h1 hc0 hb0
  refine le_trans hstep ?_
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by linarith
  have hn2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  have h5 : (2 : ℝ) ≤ (n : ℝ) ^ 5 := by
    have h3 : (3 : ℝ) ^ 5 ≤ (n : ℝ) ^ 5 := by gcongr
    norm_num at h3
    linarith
  have hslack : 2 * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 7 * Real.log n := by
    have ha : 2 * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 7 := by
      nlinarith [mul_nonneg hn2 (by linarith : (0 : ℝ) ≤ (n : ℝ) ^ 5 - 2)]
    have hc : (n : ℝ) ^ 7 ≤ (n : ℝ) ^ 7 * Real.log n := by
      nlinarith [hlog1, pow_nonneg hn0 7]
    linarith
  have hexp : (16 * (n : ℝ) ^ 5 * Real.log n + 1) * ((n : ℝ) ^ 2 * 2)
      = 32 * (n : ℝ) ^ 7 * Real.log n + 2 * (n : ℝ) ^ 2 := by ring
  rw [hexp]
  linarith

/-- **The chain's total failure probability at the adopted parameters.** -/
theorem failure_le {n : ℕ} (hn : 3 ≤ n) {q : ℝ}
    (hq : q ≤ 4 * Real.exp (-(n : ℝ))
      + ((ChainWiring.numStepsAdopted n : ℕ) : ℝ)
        * ((Fintype.card (UT n) : ℝ) * (2 * Real.exp (-(n : ℝ))))) :
    q ≤ (33 * (n : ℝ) ^ 7 * Real.log n + 4) * Real.exp (-(n : ℝ)) := by
  have hexp : (0 : ℝ) < Real.exp (-(n : ℝ)) := Real.exp_pos _
  have hcost := stepGood_cost_le hn
  have hrw : ((ChainWiring.numStepsAdopted n : ℕ) : ℝ)
        * ((Fintype.card (UT n) : ℝ) * (2 * Real.exp (-(n : ℝ))))
      = (((ChainWiring.numStepsAdopted n : ℕ) : ℝ) * ((Fintype.card (UT n) : ℝ) * 2))
        * Real.exp (-(n : ℝ)) := by ring
  rw [hrw] at hq
  nlinarith [hq, hcost, hexp]

/-! ## 4. `hpt` at the chain

The pointwise one-step bound that `StepInputs2.driftInputs_step_chain` takes as its last
hypothesis, assembled from `ChainWiring.logDet_chain_succ` (the step's log-determinant splits as
the Gaussian part plus the lift's cost), `StepInputs2.log_det_step_unconj` (the one-step
inequality, unconjugated) and `StepInputs2.opNorm_step_le_of_stepGood` (the per-step operator-norm
bound from `stepGood`).

`StateBounds` is the invariant it needs on `A_k`.  **It is a hypothesis**: see §5. -/

section Hpt

theorem symMat_add (x y : EuclideanSpace ℝ (UT n)) :
    symMat (x + y) = symMat x + symMat y := by
  ext i j
  simp only [symMat_apply, Matrix.add_apply]
  have : (x + y) (up i j) = x (up i j) + y (up i j) := rfl
  rw [this]
  ring

theorem sum_sq_symMat (u : EuclideanSpace ℝ (UT n)) :
    ∑ i, ∑ j, (symMat u i j) ^ 2 = ‖u‖ ^ 2 := by
  have h := sum_symMat_mul_eq_inner u u
  rw [real_inner_self_eq_norm_sq] at h
  rw [← h]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- **The chain's state invariant on the good event.**  `A_k` is positive definite with a uniform
lower bound `m` on its quadratic form, a uniform upper bound `M` on its operator norm, and a
symmetric congruence factor `S` with `S A_k S = 1`. -/
structure StateBounds (A : Matrix (Fin n) (Fin n) ℝ) (m M : ℝ) : Prop where
  posDef : A.PosDef
  mpos : 0 < m
  lower : ∀ x : EuclideanSpace ℝ (Fin n),
    m * ‖x‖ ^ 2 ≤ ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) A x⟫
  Mpos : 0 < M
  upper : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ ≤ M
  congr : ∃ S : Matrix (Fin n) (Fin n) ℝ, S.IsHermitian ∧ S * A * S = 1

variable {Ω : Type*} {ι : Type*} [DecidableEq ι] {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι}
  {A₀ : EuclideanSpace ℝ (UT n)} {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

/-- **`hpt` for one step and one path.**  With `V k ω = π_k (A_k⁻¹)` and
`c = 1 / (2 M² (1+δ)²)`, this is exactly the inequality
`StepInputs2.driftInputs_step_chain` consumes. -/
theorem hpt_step {k : ℕ} {ω : Ω} {m M δ η : ℝ}
    (hSB : StateBounds (symMat (Chain.chain q W A₀ ξ k ω).1) m M)
    (hη : ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
      (symMat ((Chain.freeSub q (Chain.chain q W A₀ ξ k ω).2).starProjection (ξ k ω)))‖ ≤ η)
    (hδ : η / m ≤ δ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    ChainWiring.logDet (Chain.chain q W A₀ ξ (k + 1) ω).1
      ≤ ChainWiring.logDet (Chain.chain q W A₀ ξ k ω).1
        + ⟪(Chain.freeSub q (Chain.chain q W A₀ ξ k ω).2).starProjection
            (matToUT (symMat (Chain.chain q W A₀ ξ k ω).1)⁻¹), ξ k ω⟫
        - (1 / (2 * M ^ 2 * (1 + δ) ^ 2))
          * ‖(Chain.freeSub q (Chain.chain q W A₀ ξ k ω).2).starProjection (ξ k ω)‖ ^ 2
        + ChainWiring.chainErr q W A₀ ξ k ω := by
  obtain ⟨S, hSherm, hSA⟩ := hSB.congr
  set A := symMat (Chain.chain q W A₀ ξ k ω).1 with hA
  set u := (Chain.freeSub q (Chain.chain q W A₀ ξ k ω).2).starProjection (ξ k ω) with hu
  have hAsymm : A.IsSymm := symMat_isSymm _
  have hH : (symMat u).IsHermitian := Matrix.isHermitian_iff_isSymm.2 (symMat_isSymm u)
  have hstep := StepInputs2.log_det_step_unconj hSB.posDef hSherm hSA hH hSB.mpos hSB.lower hη
    hδ hδ0 hδ1 hSB.upper hSB.Mpos
  have hsplit : ChainWiring.logDet (Chain.chain q W A₀ ξ (k + 1) ω).1
      = ChainWiring.logDet (ChainWiring.preState q W A₀ ξ k ω)
        + ChainWiring.chainErr q W A₀ ξ k ω := ChainWiring.logDet_chain_succ k ω
  have hpre : ChainWiring.logDet (ChainWiring.preState q W A₀ ξ k ω)
      = Real.log (A + symMat u).det := by
    rw [ChainWiring.logDet, ChainWiring.preState, symMat_add]
  have htr : (A⁻¹ * symMat u).trace
      = ⟪(Chain.freeSub q (Chain.chain q W A₀ ξ k ω).2).starProjection (matToUT A⁻¹), ξ k ω⟫ := by
    rw [trace_mul_symMat_eq_inner hAsymm.inv u, hu,
      StepInputs2.inner_starProjection_swap]
  have hfrob : (∑ i, ∑ j, (symMat u i j) ^ 2) / (2 * M ^ 2 * (1 + δ) ^ 2)
      = (1 / (2 * M ^ 2 * (1 + δ) ^ 2)) * ‖u‖ ^ 2 := by
    rw [sum_sq_symMat u]
    ring
  have hlogA : ChainWiring.logDet (Chain.chain q W A₀ ξ k ω).1 = Real.log A.det := rfl
  rw [hsplit, hpre, hlogA]
  rw [htr, hfrob] at hstep
  linarith [hstep.2]

end Hpt

/-! ## 3. The head-room, and `c₀` -/

/-- **The good event costs head-room, not the constant.**  `exists_mem_le_of_integral_le` applies
with `M' = M + 1` as soon as the failure probability times the head-room is below `1`; the
constant `c₀ = e^{−C'/2}` of `Assembly.volume_ge_of_logDet_le` is positive whatever `C'` is, so
widening the good event moves the *threshold* and never the sign. -/
theorem hroom_of_small_failure {M m₀ q : ℝ} (hsmall : q * (M + 1 - m₀) < 1) :
    M < M + 1 - q * (M + 1 - m₀) := by linarith

theorem c₀_pos (C' : ℝ) : 0 < Real.exp (-C' / 2) := Real.exp_pos _


/-! ## 5. What `Remaining.large` still needs — the residual, named

`hpt_step` (§4) turns the chain's one-step bound into `driftInputs_step_chain`'s hypothesis
**given** `StateBounds` on `A_k`.  That invariant is the residual, and it is not proved anywhere:

* it cannot be got step by step — `A_k − a₀·Id` accumulates `k` increments of size `η ≈ n⁻²` and
  `N·η ≈ 16 n³ log n` is useless — it has to come from the **accumulated** Gaussian bound, i.e.
  from Corollary 3.2 applied to `Σ_{j<k} π_j ξ_j` for every `k ≤ N`;
* that in turn needs the **Maurey induction over `k`**, `Σ_{j<k}(π_j ± π̃_j)ξ_j ~ N(0, kh·Id)`,
  which report 6 §6 gap 2 explicitly left to the chain module (≈ 140 lines) and which no brief has
  written.

So the residual is named here with its exact signature rather than guessed at (rule 12). -/

section Residual

variable {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [DecidableEq ι]

/-- **The residual.**  On the chain's good event, every state `A_k` with `k < N` satisfies the
invariant of §4.  Its proof route is the Maurey induction plus `GoodEvent.lowerBound_of_opNorm_le`
and `opNorm_sq_le_of_lowerBound`; its consumer is `hpt_of_stateInvariant`. -/
def StateInvariant (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι)
    (A₀ : EuclideanSpace ℝ (UT n)) (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n))
    (G : Ω → Matrix (Fin n) (Fin n) ℝ) (r : ℝ) (N : ℕ) (η m M : ℝ) : Prop :=
  ∀ k, k < N → ∀ ω ∈ chainGood G r ξ N η,
    StateBounds (symMat (Chain.chain q W A₀ ξ k ω).1) m M

/-- **`hpt` for the whole chain**, from the residual and `stepGood`.  This is the last hypothesis
of `StepInputs2.driftInputs_step_chain`, in its exact shape. -/
theorem hpt_of_stateInvariant {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι}
    {A₀ : EuclideanSpace ℝ (UT n)} {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}
    {G : Ω → Matrix (Fin n) (Fin n) ℝ} {r : ℝ} {N : ℕ} {η m M δ : ℝ}
    (hinv : StateInvariant q W A₀ ξ G r N η m M)
    (hδ : η / m ≤ δ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    ∀ k, k < N → ∀ ω ∈ chainGood G r ξ N η,
      ChainWiring.logDet (Chain.chain q W A₀ ξ (k + 1) ω).1
        ≤ ChainWiring.logDet (Chain.chain q W A₀ ξ k ω).1
          + ⟪(Chain.freeSub q (Chain.chain q W A₀ ξ k ω).2).starProjection
              (matToUT (symMat (Chain.chain q W A₀ ξ k ω).1)⁻¹), ξ k ω⟫
          - (1 / (2 * M ^ 2 * (1 + δ) ^ 2))
            * ‖(Chain.freeSub q (Chain.chain q W A₀ ξ k ω).2).starProjection (ξ k ω)‖ ^ 2
          + ChainWiring.chainErr q W A₀ ξ k ω := by
  intro k hk ω hω
  exact hpt_step (hinv k hk ω hω)
    (StepInputs2.opNorm_step_le_of_stepGood (mem_chainGood.1 hω).2 hk _) hδ hδ0 hδ1

end Residual

end Submission.L10.Discharge

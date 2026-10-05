/-
Gate L-10 (`klartag_packing`), brief 96b — the two per-step side conditions of
`LogDetChainLower.logDet_chain_ge_martingale`, discharged from `goodCut`.

`logDet_chain_ge_martingale` asks for, at every `j < K`, the state bounds at index `j` and a
ceiling `‖H_j‖_op ≤ r·m` on the one-step increment.  Both are already inside `goodCut`:

* `GoodPathBounds.stateGood_of_goodCut` hands out the state conditions at **every** index `j ≤ K`,
  not just at `K`, so `stateBounds_goodCut_le` is `GoodPathBounds.stateBounds_goodCut`'s proof run
  at a free index.
* the increment is `gaussStep_j + liftStep_j`; `goodCut` caps the raw step at `η`
  (`stateGood`'s first field — note it bounds `‖ξ_j‖`, not only the projection), and
  `StateInvariant2.norm_liftStep_le` charges the lift `card(newActive_j)·‖gaussStep_j‖`, with the
  count below `c₃` because `newActive_j ⊆ C_{j+1}` and `j + 1 ≤ K`.  So `‖H_j‖ ≤ (1 + c₃)·η`.

**The resulting `r` is `(1 + c₃)η/m`, and it decays.**  `c₃η ≤ 2/⁴√n` (`DriftStopped6d.c3eta_le`),
so `r` is `2.9·10⁻²` at `n₁` and `10⁻²⁵` at `n = 10¹⁰⁰`.  The lower bound's coefficient
`(1/2 + 2r)/m²` therefore starts at `0.734` and falls to `1/2`, against the drift's gain
`cq = 1/(2M²(1+δ)²)` which rises from `0.421` to `1/2`.  Their difference times `T·dim = 8 log n`
is `36` at `n₁` and tends to `0`, so the Markov ratio peaks at `7.5·10⁻⁵` and is uniform.

Nothing reported is edited.
-/
import Submission.L10.LogDetChainLower
import Submission.L10.GoodPathBounds

set_option linter.unusedSectionVars false

namespace Submission.L10.CutSideConditions

open MeasureTheory Matrix Finset Module
open scoped RealInnerProductSpace
open Submission.L10 Submission.L10.Increments Submission.L10.StoppedChain
open Submission.L10.GoodPathBounds

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι] {Ω : Type*} [MeasurableSpace Ω]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

/-! ## 1. The state bounds at every index below the cut -/

/-- **`GoodPathBounds.stateBounds_goodCut` at a free index `j ≤ K`.** -/
theorem stateBounds_goodCut_le {r : ℝ} {Wacc : Ω → EuclideanSpace ℝ (UT n)} {thr : ℝ} {N : ℕ}
    {η a₀ r₀ c₃ : ℝ} {K j : ℕ} {ω : Ω}
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃) (hlt : r₀ + c₃ * η < a₀)
    (hω : ω ∈ goodCut r Wacc ξ thr N η q W A₀ r₀ c₃ K) (hKN : K < N) (hj : j ≤ K) :
    Discharge.StateBounds (symMat (Chain.chain q W A₀ ξ j ω).1)
      (a₀ - (r₀ + c₃ * η)) (a₀ + (r₀ + c₃ * η)) := by
  have hstate := stateGood_of_goodCut hω hKN hj
  have hstep : ∀ i, i < j → ‖StateInvariant.gaussStep q W A₀ ξ i ω‖ ≤ η := fun i hi =>
    le_trans (Submodule.norm_starProjection_apply_le _ _) (hstate.1 i hi)
  have hlift : ‖StateInvariant.liftSum q W A₀ ξ j ω‖ ≤ c₃ * η := by
    refine le_trans (LiftBound.norm_liftSum_le_card hA₀ hq hne hη j ω hstep) ?_
    exact mul_le_mul_of_nonneg_right hstate.2.2 hη
  exact LiftBound.stateBounds_of_chain_count hA₀ hq hne hA₀m hr₀ (by positivity)
    hstate.2.1 hlift hlt

/-! ## 2. The per-step increment, capped -/

/-- **`card (newActive j) ≤ c₃`** on `goodCut`, for `j < K`: the newly frozen constraints at step
`j` all sit in `C_{j+1}`. -/
theorem card_newActive_le {r : ℝ} {Wacc : Ω → EuclideanSpace ℝ (UT n)} {thr : ℝ} {N : ℕ}
    {η r₀ c₃ : ℝ} {K j : ℕ} {ω : Ω}
    (hω : ω ∈ goodCut r Wacc ξ thr N η q W A₀ r₀ c₃ K) (hKN : K < N) (hj : j < K) :
    ((Chain.newActive q W A₀ ξ j ω).card : ℝ) ≤ c₃ := by
  classical
  have hsub : Chain.newActive q W A₀ ξ j ω ⊆ (Chain.chain q W A₀ ξ (j + 1) ω).2 := by
    rw [Chain.chain_snd_succ_eq]; exact Finset.subset_union_right
  have hcard : ((Chain.newActive q W A₀ ξ j ω).card : ℝ)
      ≤ ((Chain.chain q W A₀ ξ (j + 1) ω).2.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  exact le_trans hcard (stateGood_of_goodCut hω hKN (by omega)).2.2

/-- **The one-step increment is at most `(1 + c₃)·η`** — the raw step plus the worst case in which
every remaining constraint freezes at that one step. -/
theorem norm_incr_le {r : ℝ} {Wacc : Ω → EuclideanSpace ℝ (UT n)} {thr : ℝ} {N : ℕ}
    {η r₀ c₃ : ℝ} {K j : ℕ} {ω : Ω}
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hω : ω ∈ goodCut r Wacc ξ thr N η q W A₀ r₀ c₃ K) (hKN : K < N) (hj : j < K) :
    ‖LogDetChainLower.incr q W A₀ ξ j ω‖ ≤ (1 + c₃) * η := by
  have hg : ‖StateInvariant.gaussStep q W A₀ ξ j ω‖ ≤ η :=
    le_trans (Submodule.norm_starProjection_apply_le _ _)
      ((stateGood_of_goodCut hω hKN (by omega : j + 1 ≤ K)).1 j (by omega))
  have hg0 : (0 : ℝ) ≤ ‖StateInvariant.gaussStep q W A₀ ξ j ω‖ := norm_nonneg _
  have hcard := card_newActive_le hω hKN hj
  have hl : ‖StateInvariant.liftStep q W A₀ ξ j ω‖ ≤ c₃ * η := by
    refine le_trans (StateInvariant2.norm_liftStep_le hA₀ hq hne j ω) ?_
    calc ((Chain.newActive q W A₀ ξ j ω).card : ℝ)
          * ‖StateInvariant.gaussStep q W A₀ ξ j ω‖
        ≤ c₃ * ‖StateInvariant.gaussStep q W A₀ ξ j ω‖ :=
          mul_le_mul_of_nonneg_right hcard hg0
      _ ≤ c₃ * η := by
          have hc0 : (0 : ℝ) ≤ c₃ := le_trans (Nat.cast_nonneg _) hcard
          exact mul_le_mul_of_nonneg_left hg hc0
  rw [LogDetChainLower.incr_eq]
  calc ‖StateInvariant.gaussStep q W A₀ ξ j ω + StateInvariant.liftStep q W A₀ ξ j ω‖
      ≤ ‖StateInvariant.gaussStep q W A₀ ξ j ω‖
        + ‖StateInvariant.liftStep q W A₀ ξ j ω‖ := norm_add_le _ _
    _ ≤ η + c₃ * η := add_le_add hg hl
    _ = (1 + c₃) * η := by ring

/-- The operator-norm form, which is what the one-step lower bound reads. -/
theorem opNorm_incr_le {r : ℝ} {Wacc : Ω → EuclideanSpace ℝ (UT n)} {thr : ℝ} {N : ℕ}
    {η r₀ c₃ : ℝ} {K j : ℕ} {ω : Ω}
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hω : ω ∈ goodCut r Wacc ξ thr N η q W A₀ r₀ c₃ K) (hKN : K < N) (hj : j < K) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
        (symMat (LogDetChainLower.incr q W A₀ ξ j ω))‖ ≤ (1 + c₃) * η :=
  le_trans (StepInputs2.opNorm_symMat_le_norm _) (norm_incr_le hA₀ hq hne hω hKN hj)

/-! ## 3. The pathwise lower bound on `goodCut`, side conditions discharged -/

/-- **The pathwise lower bound, with nothing left per step.**  The only numeric hypothesis is
`hrm : (1 + c₃)·η ≤ rr · (a₀ − (r₀ + c₃η))` with `rr ≤ 1/2`, which `DriftStopped6d.c3eta_le`
supplies with a factor of ten to spare at every `n ≥ n₁`. -/
theorem logDet_ge_of_goodCut {r : ℝ} {Wacc : Ω → EuclideanSpace ℝ (UT n)} {thr : ℝ} {N : ℕ}
    {η a₀ r₀ c₃ rr : ℝ} {K : ℕ} {ω : Ω} {xs : ι → (Fin n → ℝ)}
    (hqx : q = fun i => ChainWiring.qUT (xs i))
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃) (hlt : r₀ + c₃ * η < a₀)
    (hrr0 : 0 ≤ rr) (hrr : rr ≤ 1 / 2)
    (hrm : (1 + c₃) * η ≤ rr * (a₀ - (r₀ + c₃ * η)))
    (hω : ω ∈ goodCut r Wacc ξ thr N η q W A₀ r₀ c₃ K) (hKN : K < N) :
    ChainWiring.logDet A₀
        + (∑ j ∈ Finset.range K,
            ⟪LogDetChainLower.Vcoef q W A₀ ξ j ω, ξ j ω⟫)
        - ((1 / 2 + 2 * rr) / (a₀ - (r₀ + c₃ * η)) ^ 2)
            * (∑ j ∈ Finset.range K, ‖LogDetChainLower.incr q W A₀ ξ j ω‖ ^ 2)
      ≤ ChainWiring.logDet (Chain.chain q W A₀ ξ K ω).1 := by
  subst hqx
  exact LogDetChainLower.logDet_chain_ge_martingale (xs := xs) (W := W) (A₀ := A₀) (ξ := ξ)
    (m := a₀ - (r₀ + c₃ * η)) (M := a₀ + (r₀ + c₃ * η)) hrr0 hrr K
    (fun j hj => stateBounds_goodCut_le hA₀ hq hne hA₀m hη hr₀ hc₃ hlt hω hKN (le_of_lt hj))
    (fun j hj => le_trans (opNorm_incr_le hA₀ hq hne hω hKN hj) hrm)


/-! ## 4. The numeric side condition at the adopted parameters, uniform in `n` -/

section Numeric

/-- **`rr := 5/⁴√n`** — the ceiling the increment actually needs, and it decays.  At `n₁` it is
`0.132`; the resulting coefficient `(1/2 + 2rr)/m²` is `0.92` there and tends to `1/2`. -/
noncomputable def rrAt (n : ℕ) : ℝ := 5 / Real.sqrt (Real.sqrt (n : ℝ))

theorem rrAt_nonneg (n : ℕ) : 0 ≤ rrAt n := by
  rw [rrAt]; positivity

theorem rrAt_le_half {n : ℕ} (hn : 2073600 ≤ n) : rrAt n ≤ 1 / 2 := by
  have hq : (37 : ℝ) ≤ Real.sqrt (Real.sqrt (n : ℝ)) := WindowR.qrt_ge hn
  have hq0 : (0 : ℝ) < Real.sqrt (Real.sqrt (n : ℝ)) := by linarith
  rw [rrAt, div_le_iff₀ hq0]
  linarith

/-- **The increment ceiling, proved uniformly.**  `η ≤ √2/n³` (`ParamsAdopted2.eta2_le`) and
`c₃''·η ≤ 2/⁴√n` (`DriftStopped6c.c3eta_le`), against `rr·m ≥ 2.5/⁴√n` from `mAt ≥ 1/2`. -/
theorem incr_cap_le {n : ℕ} (hn : 2073600 ≤ n) :
    (1 + DriftStopped6c.c3Adopted'' n) * DriftStopped6.etaAdopted n
      ≤ rrAt n * GoodPathBounds.mAt n (DriftStopped6c.c3Adopted'' n) := by
  have hn3 : 3 ≤ n := by omega
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hq : (37 : ℝ) ≤ Real.sqrt (Real.sqrt (n : ℝ)) := WindowR.qrt_ge hn
  have hq0 : (0 : ℝ) < Real.sqrt (Real.sqrt (n : ℝ)) := by linarith
  have hsq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hn0.le
  have hsq0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have h1 : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by nlinarith [hsq, hsq0, hnR]
  have hqq : Real.sqrt (Real.sqrt (n : ℝ)) ^ 2 = Real.sqrt (n : ℝ) :=
    Real.sq_sqrt hsq0
  have h2 : Real.sqrt (Real.sqrt (n : ℝ)) ≤ Real.sqrt (n : ℝ) := by
    nlinarith [hqq, hq0, hq]
  have hqn : Real.sqrt (Real.sqrt (n : ℝ)) ≤ (n : ℝ) := by linarith
  -- the two tree bounds
  have heta : DriftStopped6.etaAdopted n ≤ Real.sqrt 2 / (n : ℝ) ^ 3 := by
    rw [DriftStopped6.etaAdopted]; exact ParamsAdopted2.eta2_le hn3
  have heta0 : 0 ≤ DriftStopped6.etaAdopted n := by
    rw [DriftStopped6.etaAdopted]; positivity
  have hc3eta : DriftStopped6c.c3Adopted'' n * DriftStopped6.etaAdopted n
      ≤ 2 / Real.sqrt (Real.sqrt (n : ℝ)) := DriftStopped6c.c3eta_le hn
  have hm : (1 : ℝ) / 2 ≤ GoodPathBounds.mAt n (DriftStopped6c.c3Adopted'' n) :=
    GoodPathBounds.half_le_mAt hn (DriftStopped6c.c3Adopted''_eta_le hn)
  -- `√2/n³ ≤ 1/(2·⁴√n)`
  have hs2 : Real.sqrt 2 ≤ 2 := by
    rw [show (2:ℝ) = Real.sqrt 4 by rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq]; norm_num]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hn2 : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith [hnR, hn0]
  have h4n : (4 : ℝ) * (n : ℝ) ≤ (n : ℝ) ^ 3 := by nlinarith [hn2, hn0]
  have hcube : Real.sqrt 2 * (2 * Real.sqrt (Real.sqrt (n : ℝ))) ≤ (n : ℝ) ^ 3 := by
    nlinarith [hs2, hqn, h4n, hq0, Real.sqrt_nonneg (2:ℝ)]
  have hsmall : Real.sqrt 2 / (n : ℝ) ^ 3 ≤ 1 / (2 * Real.sqrt (Real.sqrt (n : ℝ))) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith [hcube]
  -- assemble
  have hlhs : (1 + DriftStopped6c.c3Adopted'' n) * DriftStopped6.etaAdopted n
      = DriftStopped6.etaAdopted n
        + DriftStopped6c.c3Adopted'' n * DriftStopped6.etaAdopted n := by ring
  have hrhs : rrAt n * GoodPathBounds.mAt n (DriftStopped6c.c3Adopted'' n)
      ≥ (5 / Real.sqrt (Real.sqrt (n : ℝ))) * (1 / 2) := by
    rw [rrAt]
    exact mul_le_mul_of_nonneg_left hm (by positivity)
  have hfive : (5 / Real.sqrt (Real.sqrt (n : ℝ))) * (1 / 2)
      = 2 / Real.sqrt (Real.sqrt (n : ℝ)) + 1 / (2 * Real.sqrt (Real.sqrt (n : ℝ))) := by
    field_simp; ring
  rw [hlhs]
  have hstep : DriftStopped6.etaAdopted n
      + DriftStopped6c.c3Adopted'' n * DriftStopped6.etaAdopted n
      ≤ 1 / (2 * Real.sqrt (Real.sqrt (n : ℝ))) + 2 / Real.sqrt (Real.sqrt (n : ℝ)) :=
    add_le_add (le_trans heta hsmall) hc3eta
  linarith [hrhs, hfive.symm.le, hfive.le]

end Numeric

end Submission.L10.CutSideConditions

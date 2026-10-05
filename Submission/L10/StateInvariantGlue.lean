import Submission.L10.StateInvariant
import Submission.L10.DischargeGlue

/-!
# Gate L-10 (`klartag_packing`), brief 29 — the state invariant on `StepGlue.chainGood`

Brief 29's route addition.  `Submission/L10/StateInvariant.lean` proves the invariant against
`Discharge.StateInvariant`, whose good event `Discharge.chainGood` has its accumulated half on the
*matrix* carrier.  `Submission/L10/DischargeGlue.lean` (report 25 §9b) restated the residual as
`DischargeGlue.StateInvariant` on `StepGlue.chainGood`, i.e. on the `UT n` carrier, which is the
tree's currency.  Both files are reported and frozen (rule 5), so the bridge lives here.

The mathematics is unchanged: the per-`(k, ω)` core `stateBounds_of_chain` depends on the good
event only through the two bounds it supplies, so it serves either event.  What changes is which
`StateInvariant` the discharge successor can consume without restating anything.
-/

set_option linter.unusedSectionVars false

namespace Submission.L10.StateInvariantGlue

open MeasureTheory Matrix Finset Module ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace
open Submission.L10 Submission.L10.Increments Submission.L10.StateInvariant

noncomputable section

variable {n : ℕ} {ι : Type*} [DecidableEq ι] {Ω : Type*} [MeasurableSpace Ω]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

/-- **The per-path core, independent of which good event is used.**  `A_k = A₀ + gaussSum +
liftSum`; bound the two sums and read off `StateBounds`. -/
theorem stateBounds_of_chain {a₀ r₀ ε : ℝ} {k : ℕ} {ω : Ω}
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hε0 : 0 ≤ ε) (hr₀ : 0 ≤ r₀)
    (hacc : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat (gaussSum q W A₀ ξ k ω))‖ ≤ r₀)
    (hlift : ∀ j, j < k → ‖liftStep q W A₀ ξ j ω‖ ≤ ε)
    (hlt : r₀ + (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) * ε < a₀) :
    Discharge.StateBounds (symMat (Chain.chain q W A₀ ξ k ω).1)
      (a₀ - (r₀ + (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) * ε))
      (a₀ + (r₀ + (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) * ε)) := by
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
  refine (norm_add_le _ _).trans (add_le_add hacc ?_)
  exact (StepInputs2.opNorm_symMat_le_norm _).trans
    (norm_liftSum_le hA₀ hq hne hε0 k ω hlift)

/-- **R1 against `DischargeGlue.StateInvariant`** — the form the discharge successor consumes with
no restatement. -/
theorem stateInvariant_of_chainGood
    {r : ℝ} {Wacc : Ω → EuclideanSpace ℝ (UT n)} {thr : ℝ} {N : ℕ} {η a₀ r₀ ε : ℝ}
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hε0 : 0 ≤ ε) (hr₀ : 0 ≤ r₀)
    (hacc : ∀ k, k < N → ∀ ω ∈ StepGlue.chainGood r Wacc ξ thr N η,
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat (gaussSum q W A₀ ξ k ω))‖ ≤ r₀)
    (hlift : ∀ k, k < N → ∀ ω ∈ StepGlue.chainGood r Wacc ξ thr N η, ∀ j, j < k →
      ‖liftStep q W A₀ ξ j ω‖ ≤ ε)
    (hlt : r₀ + (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) * ε < a₀) :
    DischargeGlue.StateInvariant q W A₀ ξ r Wacc thr N η
      (a₀ - (r₀ + (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) * ε))
      (a₀ + (r₀ + (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) * ε)) := fun k hk ω hω =>
  stateBounds_of_chain hA₀ hq hne hA₀m hε0 hr₀ (hacc k hk ω hω) (hlift k hk ω hω) hlt

/-- …and with the accumulated bound read off `accGood`. -/
theorem stateInvariant_of_accGood
    {r : ℝ} {Wacc : Ω → EuclideanSpace ℝ (UT n)} {thr : ℝ} {N : ℕ} {η a₀ r₀ ε : ℝ}
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hε0 : 0 ≤ ε) (hr₀ : 0 ≤ r₀)
    (hsub : StepGlue.chainGood r Wacc ξ thr N η ⊆ accGood q W A₀ ξ N r₀)
    (hlift : ∀ k, k < N → ∀ ω ∈ StepGlue.chainGood r Wacc ξ thr N η, ∀ j, j < k →
      ‖liftStep q W A₀ ξ j ω‖ ≤ ε)
    (hlt : r₀ + (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) * ε < a₀) :
    DischargeGlue.StateInvariant q W A₀ ξ r Wacc thr N η
      (a₀ - (r₀ + (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) * ε))
      (a₀ + (r₀ + (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) * ε)) :=
  stateInvariant_of_chainGood hA₀ hq hne hA₀m hε0 hr₀
    (fun k hk _ hω => hsub hω k hk) hlift hlt

/-- **`hpt` at the chain, with the invariant discharged** — `DischargeGlue.hpt_of_stateInvariant`
composed with the above, so the only inputs left are the accumulated event, the per-freeze lift
bound and the numeric condition. -/
theorem hpt_of_chainGood
    {r : ℝ} {Wacc : Ω → EuclideanSpace ℝ (UT n)} {thr : ℝ} {N : ℕ} {η a₀ r₀ ε δ : ℝ}
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hε0 : 0 ≤ ε) (hr₀ : 0 ≤ r₀)
    (hsub : StepGlue.chainGood r Wacc ξ thr N η ⊆ accGood q W A₀ ξ N r₀)
    (hlift : ∀ k, k < N → ∀ ω ∈ StepGlue.chainGood r Wacc ξ thr N η, ∀ j, j < k →
      ‖liftStep q W A₀ ξ j ω‖ ≤ ε)
    (hlt : r₀ + (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) * ε < a₀)
    (hδ : η / (a₀ - (r₀ + (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) * ε)) ≤ δ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    ∀ k, k < N → ∀ ω ∈ StepGlue.chainGood r Wacc ξ thr N η,
      ChainWiring.logDet (Chain.chain q W A₀ ξ (k + 1) ω).1
        ≤ ChainWiring.logDet (Chain.chain q W A₀ ξ k ω).1
          + ⟪(Chain.freeSub q (Chain.chain q W A₀ ξ k ω).2).starProjection
              (Discharge.matToUT (symMat (Chain.chain q W A₀ ξ k ω).1)⁻¹), ξ k ω⟫
          - (1 / (2 * (a₀ + (r₀ + (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) * ε)) ^ 2
              * (1 + δ) ^ 2))
            * ‖(Chain.freeSub q (Chain.chain q W A₀ ξ k ω).2).starProjection (ξ k ω)‖ ^ 2
          + ChainWiring.chainErr q W A₀ ξ k ω :=
  DischargeGlue.hpt_of_stateInvariant
    (stateInvariant_of_accGood hA₀ hq hne hA₀m hε0 hr₀ hsub hlift hlt) hδ hδ0 hδ1

end

end Submission.L10.StateInvariantGlue

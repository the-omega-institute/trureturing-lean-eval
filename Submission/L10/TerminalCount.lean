import Submission.L10.DriftStopped8

/-!
# Gate L-10 (`klartag_packing`) — the terminal contact count

Brief 74.  Report 62b's correction: `Theorem2.chainW` is `ContactIntegrated.intWeight`, the
**time-integrated** count, which feeds `ContactIntegrated.sum_free_ge` and so the drift's free
dimension.  `StateInvariant4.measureReal_compl_countGood_le_expected` wants a bound on the
**terminal** count `E|C_N|`, and report 37's `hitting_tail_forces_zero` records that the two are not
interchangeable.  This module supplies the terminal one.

## What the derivation actually needs

`ChainWalk.hsteps_of_walk` already proves `P.real {ω | y ∈ C_k ω} ≤ 4·profStep α n h y k` for
**every** `k < N`, straight from `TailSideHyp` (= its `hprop`).  So the terminal bound is that
statement read at the index the count event uses, and **no monotonicity step is required**:
`Chain.chain_snd_mono` runs the other way (from a bound at `K` down to `k ≤ K`), which is the free
direction.  What monotonicity does buy is recorded in the report: `intWeight y ≥ (T − kh)·P(y ∈ C_k)`,
so the integrated weight alone bounds the terminal count at index `k` with loss `1/(T − kh)` —
`≈ n⁹` at `k = N − 1`, which is why a separate terminal weight is needed at all.

* `terminal_tail_of_hsteps`, `terminal_tail` — the bound in the **exact `htail` shape**
  (`2·weight + err`, `err = 0`), so `measureReal_compl_countGood_le_expected` applies verbatim.
* `countGood_of_terminal_weight` — the count event's failure bound from a §5 sum over the window.
* `sums_of_combined` — one §5 selection, two thresholds: the combined weight `c₁w₁ + c₂w₂`.
-/

set_option linter.unusedSectionVars false

namespace Submission.L10.TerminalCount

open MeasureTheory Matrix Finset Module Submission.L10 Submission.L10.Increments
open Submission.L10.ConstructionA Submission.L10.Tiling Submission.L10.PaddedLawSetup
open Submission.L10.ChainSetup
open scoped ENNReal RealInnerProductSpace

/-! ## 1. The terminal weight, in `htail`'s shape -/

section Terminal

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {q : (Fin n → ℤ) → EuclideanSpace ℝ (UT n)} {W : Finset (Fin n → ℤ)}
  {A₀ : EuclideanSpace ℝ (UT n)} {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)} {α : ℝ}

/-- **The terminal contact bound, in the exact shape `htail` consumes** — `2·weight + err` with
`weight y = 2·profStep α n h y K` and `err = 0`. -/
theorem terminal_tail_of_hsteps {K : ℕ}
    (hsteps : ∀ k, k < ParamsAdopted2.numStepsAdopted2 n → ∀ y ∈ W,
      P.real {ω | y ∈ contactSet q W A₀ ξ k ω}
        ≤ 4 * profStep α n (ParamsAdopted2.stepSizeAdopted2 n) y k)
    (hK : K < ParamsAdopted2.numStepsAdopted2 n) :
    ∀ y ∈ W, P.real {ω | y ∈ (Chain.chain q W A₀ ξ K ω).2}
      ≤ 2 * (2 * profStep α n (ParamsAdopted2.stepSizeAdopted2 n) y K) + 0 := by
  intro y hy
  have h := hsteps K hK y hy
  simp only [contactSet] at h
  linarith

/-- **The same, straight from `TailSideHyp`** — the tail side's one probabilistic input, read at the
index the count event uses. -/
theorem terminal_tail {c : ℝ} {K : ℕ}
    (hq : ∀ j : (Fin n → ℤ), ∀ i ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫)
    (hA₀ : ∀ y ∈ W, (1 : ℝ) < ⟪A₀, q y⟫)
    (hwin : ∀ y ∈ W, ‖toE n y‖ + Real.sqrt n / 2 ≤ windowC α n)
    (hr : ∀ y ∈ W, 0 < α * ‖toE n y‖)
    (hy : ∀ k, k < ParamsAdopted2.numStepsAdopted2 n → k ≠ 0 → ∀ y ∈ W,
      0 < yOf (a0C n) ((k : ℝ) * ParamsAdopted2.stepSizeAdopted2 n) (α * ‖toE n y‖))
    (htail : TailSideHyp n c α q W A₀)
    (hK : K < ParamsAdopted2.numStepsAdopted2 n) :
    ∀ y ∈ W, (gaussPath (EuclideanSpace ℝ (UT n))).real
        {ω | y ∈ (Chain.chain q W A₀ (step c) K ω).2}
      ≤ 2 * (2 * profStep α n (ParamsAdopted2.stepSizeAdopted2 n) y K) + 0 :=
  terminal_tail_of_hsteps (hsteps_of_walk hq hA₀ hwin hr hy htail) hK

end Terminal

/-! ## 2. `countGood`'s failure bound from a §5 sum -/

section Count

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

/-- **The drift side's second count bound.**  With the terminal weight summed below `θT` on the
window the chain is run on, the count event fails with probability at most `2θT/c₃`. -/
theorem countGood_of_terminal_weight (hξ : ∀ k, Measurable (ξ k)) {K : ℕ} {c₃ : ℝ}
    (hc₃ : 0 < c₃) (weight : ι → ℝ)
    (htail : ∀ i ∈ W, P.real {ω | i ∈ (Chain.chain q W A₀ ξ K ω).2} ≤ 2 * weight i + 0)
    {θT : ℝ} (hθ : ∑ i ∈ W, weight i ≤ θT) :
    P.real (StateInvariant4.countGood q W A₀ ξ K c₃)ᶜ ≤ (2 * θT + 0) / c₃ :=
  StateInvariant4.measureReal_compl_countGood_le_expected hξ hc₃ weight (fun _ => 0) htail hθ
    (by simp)

end Count

/-! ## 3. One §5 selection, two thresholds -/

/-- **The combined weight.**  If `c₁w₁ + c₂w₂` sums to less than `1` on the selected line and each
`cᵢ·θᵢ ≥ 1`, then both sums are below their own thresholds — so a single
`Section5.exists_good_line_of_chainData` run at `w' := c₁w₁ + c₂w₂` yields the integrated **and**
the terminal light-contact facts.  Taking `cᵢ = θᵢ⁻¹` is the brief's `w_int/θ + w_T/θ_T`. -/
theorem sums_of_combined {ι : Type*} {S : Finset ι} {w₁ w₂ : ι → ℝ≥0∞} {c₁ c₂ θ₁ θ₂ : ℝ≥0∞}
    (h : ∑ y ∈ S, (c₁ * w₁ y + c₂ * w₂ y) < 1)
    (h₁ : 1 ≤ c₁ * θ₁) (h₂ : 1 ≤ c₂ * θ₂) :
    (∑ y ∈ S, w₁ y) < θ₁ ∧ (∑ y ∈ S, w₂ y) < θ₂ := by
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h
  constructor
  · by_contra hcon
    have hge : θ₁ ≤ ∑ y ∈ S, w₁ y := not_lt.1 hcon
    have hmul : c₁ * θ₁ ≤ c₁ * ∑ y ∈ S, w₁ y := by gcongr
    have hle : c₁ * (∑ y ∈ S, w₁ y) ≤ c₁ * (∑ y ∈ S, w₁ y) + c₂ * (∑ y ∈ S, w₂ y) := le_self_add
    exact absurd (lt_of_le_of_lt hle h) (not_lt.2 (le_trans h₁ hmul))
  · by_contra hcon
    have hge : θ₂ ≤ ∑ y ∈ S, w₂ y := not_lt.1 hcon
    have hmul : c₂ * θ₂ ≤ c₂ * ∑ y ∈ S, w₂ y := by gcongr
    have hle : c₂ * (∑ y ∈ S, w₂ y) ≤ c₁ * (∑ y ∈ S, w₁ y) + c₂ * (∑ y ∈ S, w₂ y) := le_add_self
    exact absurd (lt_of_le_of_lt hle h) (not_lt.2 (le_trans h₂ hmul))

end Submission.L10.TerminalCount

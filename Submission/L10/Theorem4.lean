import Mathlib
import Submission.L10.Theorem2
import Submission.L10.LatticeData

/-!
# Gate L-10 — the drift side with coverage, and the challenge statement from it

Brief 66.  The brief names this module `Theorem3.lean`; that name was taken by report 65's second
pass and is frozen (rule 5), so this is `Theorem4.lean`.

Report 65 §6: `Theorem3.DriftSide''` is stated over `shell α (m+1)` but never receives
`LatticeData.rawData_exists'`'s coverage clause, so `W = ∅` models it and the light-contact
hypothesis goes vacuous — the earlier failure in a subtler form.  The drift side here adds that
clause, in the shape `LatticeData.mem_shell_of_shell` (`:90`) proves it.

`R` is **fixed** at `(1 − 1/(m+1))/α` rather than universally quantified.  A free `R` was half of
report 56 §2's defect, and `rawData_exists'` produces exactly this radius.
-/

set_option linter.unusedSectionVars false

open MeasureTheory Finset

namespace Submission.L10.Theorem4

open scoped ENNReal RealInnerProductSpace
open Submission.L10 Submission.L10.Increments Submission.L10.Tiling
open Submission.L10.ConstructionA Submission.L10.PaddedLawSetup
open Submission.L10.TailSideSetup2 Submission.L10.RawDataInst2 Submission.L10.Theorem2

/-- **The drift side, with coverage.**  `Theorem3.DriftSide''` plus the one fact report 65 §6
said was missing: the window really does contain every lattice point between the inner radius
and the window radius, so `W = ∅` is no longer a model of the hypothesis.

`R` is **fixed** at `(1 − 1/(m+1))/α`, not quantified: `LatticeData.rawData_exists'` produces
exactly that radius, and leaving it free was half of report 56 §2's defect. -/
def DriftSide''' (c₀ : ℝ) : Prop :=
  ∀ m : ℕ, Threshold2.n₁ ≤ m → ∀ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p) (α : ℝ),
    0 < α → ∀ (hn : 3 ≤ m + 1)
      (hraw : RawData p (m + 1) α ((1 - 1 / ((m + 1 : ℕ) : ℝ)) / α)
        (qC α) (shell α (m + 1)) (A0C (m + 1)))
      (hnd : NormData (m + 1) α (qC α) (shell α (m + 1)) (A0C (m + 1))),
      (∀ y : Fin (m + 1) → ℤ, y ≠ 0 →
        (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α < ‖toE (m + 1) y‖ →
        ‖toE (m + 1) y‖ + Real.sqrt ((m + 1 : ℕ) : ℝ) / 2 ≤ windowC α (m + 1) →
          y ∈ shell α (m + 1)) →
      ∀ (g : Fin (m + 1) → ZMod p), g ≠ 0 →
      (∀ y : Fin (m + 1) → ℤ, y ≠ 0 →
        ‖toE (m + 1) y‖ ≤ (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α → y ∉ latZ p (m + 1) g) →
      LightContact (chainW hn hraw hnd) (shell α (m + 1))
        (ENNReal.ofReal (64 * C1C α (m + 1))) g →
      Assembly.ChainOutput α g c₀

/-- **`ChainDelivers'` from the drift side with coverage**, at `rawData_exists'`'s own witnesses —
so the drift side is only ever invoked at the shell. -/
theorem chainDelivers'_of_driftSide''' {c₀ : ℝ} (hd : DriftSide''' c₀) :
    Theorem2.ChainDelivers' c₀ := by
  intro m hm
  obtain ⟨p, hp, hp0, α, hα, hn, hraw, hnd, hcov⟩ := LatticeData.rawData_exists' m hm
  exact ⟨p, hp, hp0, α, (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α, qC α, shell α (m + 1), A0C (m + 1),
    hn, hraw, hnd,
    fun g hg hfree hlight => hd m hm p hp hp0 α hα hn hraw hnd hcov g hg hfree hlight⟩

/-- **The challenge statement from the drift side with coverage.** -/
theorem klartag_packing_of_driftSide''' (h : ∃ c₀ : ℝ, 0 < c₀ ∧ DriftSide''' c₀) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      let V := EuclideanSpace ℝ (Fin (n + 1))
      ∃ φ : V →ₗ[ℝ] V, let E := φ '' Metric.ball (0 : V) 1
        (MeasureTheory.volume E : EReal) = c * n ^ 2 ∧
        {v ∈ E | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} := by
  obtain ⟨c₀, hc₀, hd⟩ := h
  exact Theorem2.klartag_packing_of_chain' hc₀ (chainDelivers'_of_driftSide''' hd)

end Submission.L10.Theorem4

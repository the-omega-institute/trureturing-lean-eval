import Mathlib
import Submission.L10.Theorem2
import Submission.L10.LatticeData

/-!
# Gate L-10 — the challenge statement from the drift side alone

Brief 65, second pass.  `Theorem2.lean` is reported and is not edited (rule 5).

`Theorem2.ChainDelivers'` still bound `q`, `W`, `A₀` and `R` existentially, which a consumer that
must *restrict* the window cannot use.  `LatticeData.rawData_exists'` (`:105`) now supplies them
by name — `qC α`, `shell α (m+1)`, `A0C (m+1)`, `R = (1−1/(m+1))/α` — and it is a theorem, so the
tail half is no longer a hypothesis at all.

What is left is `DriftSide''`, stated on those same witnesses, and

  `klartag_packing_of_drift : 0 < c₀ → DriftSide'' c₀ → (the challenge statement)`.

That is the whole gate, on one hypothesis.
-/

set_option linter.unusedSectionVars false

open MeasureTheory Finset

namespace Submission.L10.Theorem3

open scoped ENNReal RealInnerProductSpace
open Submission.L10 Submission.L10.Increments Submission.L10.Tiling
open Submission.L10.ConstructionA Submission.L10.PaddedLawSetup
open Submission.L10.TailSideSetup2 Submission.L10.RawDataInst2 Submission.L10.Theorem2

/-- **The drift side, on the tail side's own witnesses.**  `q`, `W`, `A₀` and `R` are no longer
existentially bound: they are `qC α`, `shell α (m+1)`, `A0C (m+1)` and `(1−1/(m+1))/α`, exactly
as `LatticeData.rawData_exists'` produces them. -/
def DriftSide'' (c₀ : ℝ) : Prop :=
  ∀ m : ℕ, Threshold2.n₁ ≤ m → ∀ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p) (α : ℝ),
    0 < α → ∀ (hn : 3 ≤ m + 1)
      (hraw : RawData p (m + 1) α ((1 - 1 / ((m + 1 : ℕ) : ℝ)) / α)
        (qC α) (shell α (m + 1)) (A0C (m + 1)))
      (hnd : NormData (m + 1) α (qC α) (shell α (m + 1)) (A0C (m + 1)))
      (g : Fin (m + 1) → ZMod p), g ≠ 0 →
      (∀ y : Fin (m + 1) → ℤ, y ≠ 0 →
        ‖toE (m + 1) y‖ ≤ (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α → y ∉ latZ p (m + 1) g) →
      LightContact (chainW hn hraw hnd) (shell α (m + 1))
        (ENNReal.ofReal (64 * C1C α (m + 1))) g →
      Assembly.ChainOutput α g c₀

/-- **The challenge statement from the drift side alone.**  The tail half is
`LatticeData.rawData_exists'`, a theorem, so nothing else is assumed. -/
theorem klartag_packing_of_drift {c₀ : ℝ} (hc₀ : 0 < c₀) (hd : DriftSide'' c₀) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      let V := EuclideanSpace ℝ (Fin (n + 1))
      ∃ φ : V →ₗ[ℝ] V, let E := φ '' Metric.ball (0 : V) 1
        (MeasureTheory.volume E : EReal) = c * n ^ 2 ∧
        {v ∈ E | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} := by
  refine Theorem2.klartag_packing_of_chain' hc₀ (fun m hm => ?_)
  obtain ⟨p, hp, hp0, α, hα, hn, hraw, hnd, _hcov⟩ := LatticeData.rawData_exists' m hm
  exact ⟨p, hp, hp0, α, (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α, qC α, shell α (m + 1), A0C (m + 1),
    hn, hraw, hnd, fun g hg hfree hlight => hd m hm p hp hp0 α hα hn hraw hnd g hg hfree hlight⟩

end Submission.L10.Theorem3

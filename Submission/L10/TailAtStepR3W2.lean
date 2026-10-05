import Submission.L10.TailAtStepR2W2

/-!
# Gate L-10 (`klartag_packing`), brief 85b — the producer at `windowR2`, parameterised

`TailAtStepR3` (the `windowR` lane) discharges the fold-in outright, because
`Lemma43R.radial_bound4_of_chain'` is stated **at `windowR`**.  The `windowR2` lane has no such
theorem: `WindowR2.windowR_le_windowR2` runs the wrong way for a bound on `∫ profile`, so the
substitution cannot produce it and neither can monotonicity.  This module is therefore the
`windowR` lane's `paramsProducerR'_tight` with Lemma 4.3's two outputs **as hypotheses**, restricted
to the range where they are true (`2073600 ≤ m+1`, `0 < α`) — the restriction report 84 §2 records
as necessary and harmless.

**Two inputs are missing for this lane, both upstream of me:** Lemma 4.3 at `windowR2`
(`radial_bound4_of_chain'` and `C1R` at the reach-2 endpoint), and `Theorem2R2` at `windowR2`
(its `wR`, `ParamsProducerR'` and closing line are all at `shellR`/`windowR`).  With the first,
`paramsProducerR2'_of_radial` below becomes hypothesis-free; with both, the closing line returns.
-/

set_option linter.unusedSectionVars false

namespace Submission.L10.TailAtStepR3W2

open MeasureTheory Set Real Finset
open scoped ENNReal NNReal
open Submission.L10 Submission.L10.Increments Submission.L10.ChainDataInst
open Submission.L10.Tiling Submission.L10.Section5 Submission.L10.ConstructionA
open Submission.L10.WindowR2 Submission.L10.TailAtStepR2W2

noncomputable section

/-- **The producer at `windowR2`, modulo Lemma 4.3 there.**  Every field of `Params` is supplied by
`TailAtStepR2W2.params_of_raw2R_of_radial`; the two hypotheses are exactly what a `windowR2`
re-derivation of report 71 would return. -/
theorem params_of_raw2R2 {p n : ℕ} [Fact (Nat.Prime p)] (hn : 2073600 ≤ n)
    (Q : ChainRaw2RW2 p n) {C : ℝ} (hC : 0 < C)
    (hrad : ∫ y in Ioi (0 : ℝ), y ^ (n - 1) * fR4 Q.alpha n y ≤ C) :
    (params_of_raw2R_of_radial hn Q hC hrad).alpha = Q.alpha ∧
      (params_of_raw2R_of_radial hn Q hC hrad).R = Q.R ∧
      (params_of_raw2R_of_radial hn Q hC hrad).supp = Q.supp ∧
      (params_of_raw2R_of_radial hn Q hC hrad).w = Q.w ∧
      (params_of_raw2R_of_radial hn Q hC hrad).theta
        = ENNReal.ofReal (ThetaTight.thetaTight p n C) :=
  params_fields hn Q hC hrad

/-- The same, packaged as a producer over all dimensions above the threshold. -/
theorem paramsProducerR2'_of_radial {C : ℕ → ℝ → ℝ}
    (hC : ∀ (m : ℕ) (α : ℝ), 2073600 ≤ m + 1 → 0 < α → 0 < C m α)
    (hrad : ∀ (m : ℕ) (α : ℝ), 2073600 ≤ m + 1 → 0 < α →
      ∫ y in Ioi (0 : ℝ), y ^ (m + 1 - 1) * fR4 α (m + 1) y ≤ C m α) :
    ∀ (p m : ℕ) (_ : Fact (Nat.Prime p)), 2073600 ≤ m + 1 → ∀ Q : ChainRaw2RW2 p (m + 1),
      ∃ P : Params p (m + 1), P.alpha = Q.alpha ∧ P.R = Q.R ∧ P.supp = Q.supp ∧
        P.w = Q.w ∧ P.theta
          = ENNReal.ofReal (ThetaTight.thetaTight p (m + 1) (C m Q.alpha)) := by
  intro p m hp hm Q
  exact ⟨params_of_raw2R_of_radial hm Q (hC m Q.alpha hm Q.alpha_pos)
      (hrad m Q.alpha hm Q.alpha_pos),
    params_fields hm Q (hC m Q.alpha hm Q.alpha_pos) (hrad m Q.alpha hm Q.alpha_pos)⟩

end

end Submission.L10.TailAtStepR3W2

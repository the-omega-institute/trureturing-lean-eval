import Submission.L10.StateSupply
import Submission.L10.TerminalCount

/-!
# Gate L-10 (`klartag_packing`) — `GoodPath` for **light** lines, and the free dimension it buys

Brief 82b.  **The defect is mine and the coordinator is right.**  `StateSupply.klartag_packing_final`'s
`hgood` quantifies over every `g ≠ 0`, because `stateSupplyAdoptedR_of_goodPath` introduced
`StateSupplyAdoptedR`'s R-condition and `LightContact` and then discarded both.  A path with
`logDet ≤ 2·10⁵ − 4 log n` exists only for a **light** `g`: report 80 computed `C'` from
`∑_{W_g} intWeight < θ'`, and a heavy line loses up to `|W_g|·T`.  So `hgood` is a hypothesis that
composes and cannot be proved — report 56 §2's pattern, for the third time in this lane.  The fix
is free, because `StateSupplyAdoptedR` hands both hypotheses over; §1 is the restatement.

## §2's finding: `ContactIntegrated.sum_free_ge` does **not** apply to the stopped chain

`sum_free_ge` wants `hfree : dim − |C_k| ≤ Nfun k ω` for **every** `ω`.  For the stopped free
dimension that is false after the stopping time: `DriftStopped6.stoppedFreeDim` is `0` on `{τ ≤ k}`
while `dim − |C_k|` is positive there.  `sum_free_ge_stopped` is the corrected form, with the extra
term `dim·∑_{k<m} P(τ ≤ k)`.  It costs `c·T·dim·P(τ ≤ N) ≈ 51.4 · 0.0254 ≈ 1.31` in `C'` — a
constant, against report 80's `1.72·10⁵`, so `C' = 2·10⁵` is untouched.

`StateSupply.lean` and `TerminalCount.lean` are reported and are not edited; this module imports
them.
-/

set_option linter.unusedSectionVars false

namespace Submission.L10.GoodPathLight

open MeasureTheory Matrix Finset Module Submission.L10 Submission.L10.Increments
open Submission.L10.ConstructionA Submission.L10.Tiling
open Submission.L10.PaddedLawSetupR Submission.L10.RawDataInst2R Submission.L10.RawDataInst2
open Submission.L10.DriftStopped8R Submission.L10.StateSupply
open scoped ENNReal RealInnerProductSpace

/-! ## 1. The restatement: `GoodPath` only for light lines -/

section Restated

variable {w : ∀ m : ℕ, ℝ → (Fin (m + 1) → ℤ) → ℝ≥0∞} {θ : ℕ → ℝ → ℝ≥0∞} {C' : ℝ}

/-- **The hypothesis that can actually be delivered.**  Both of `StateSupplyAdoptedR`'s per-line
hypotheses are carried: the R-condition and the light contact. -/
def LightGoodPath (w : ∀ m : ℕ, ℝ → (Fin (m + 1) → ℤ) → ℝ≥0∞) (θ : ℕ → ℝ → ℝ≥0∞)
    (C' : ℝ) : Prop :=
  ∀ m : ℕ, Threshold2.n₁ ≤ m → ∀ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p) (α : ℝ),
    0 < α → ∀ g : Fin (m + 1) → ZMod p, g ≠ 0 →
      (∀ y : Fin (m + 1) → ℤ, y ≠ 0 →
        ‖toE (m + 1) y‖ ≤ (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α → y ∉ latZ p (m + 1) g) →
      Theorem2.LightContact (w m α) (shellR α (m + 1)) (θ m α) g →
      GoodPath p m α g C'

/-- **`StateSupplyAdoptedR` from the light-line form** — same proof as
`StateSupply.stateSupplyAdoptedR_of_goodPath`, with the two hypotheses passed on instead of
dropped. -/
theorem stateSupplyAdoptedR_of_goodPath' (hgood : LightGoodPath w θ C') :
    DriftStopped8R.StateSupplyAdoptedR w θ C' := by
  intro m hm p hp hp0 α hα hn hraw hnd _hcov g hg hfree hlight
  exact stateTriple_of_goodPath hm hraw (hgood m hm p hp hp0 α hα g hg hfree hlight)

/-- **The gate, on two hypotheses, with the drift side's one now deliverable.** -/
theorem klartag_packing_final' (hpr : Theorem2R.ParamsProducerR w θ)
    (hgood : LightGoodPath w θ 200000) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      let V := EuclideanSpace ℝ (Fin (n + 1))
      ∃ φ : V →ₗ[ℝ] V, let E := φ '' Metric.ball (0 : V) 1
        (MeasureTheory.volume E : EReal) = c * n ^ 2 ∧
        {v ∈ E | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} :=
  Theorem2R.klartag_packing_of_stateSupplyR hpr (stateSupplyAdoptedR_of_goodPath' hgood)

end Restated

/-! ## 2. The light contact, read as a real sum -/

section Bridge

/-- `LightContact` at an `ENNReal.ofReal` weight family is a real inequality on the drift's own
window — `filter_eq_windowOfR` (rule 16) is what moves the index set. -/
theorem sum_lt_of_lightContact {p m : ℕ} [NeZero p] {α : ℝ} {g : Fin (m + 1) → ZMod p}
    {v : (Fin (m + 1) → ℤ) → ℝ} {Θ : ℝ} (hv : ∀ y, 0 ≤ v y) (hΘ : 0 < Θ)
    (h : Theorem2.LightContact (fun y => ENNReal.ofReal (v y)) (shellR α (m + 1))
      (ENNReal.ofReal Θ) g) :
    ∑ y ∈ windowOfR α p m g, v y < Θ := by
  classical
  have h' : ∑ y ∈ (shellR α (m + 1)).filter (fun y => y ∈ latZ p (m + 1) g),
      ENNReal.ofReal (v y) < ENNReal.ofReal Θ := h
  rw [filter_eq_windowOfR] at h'
  rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ => hv y)] at h'
  exact (ENNReal.ofReal_lt_ofReal_iff hΘ).1 h'

end Bridge

/-! ## 3. The free dimension of the **stopped** chain -/

section FreeDim

variable {ι : Type*} [DecidableEq ι] {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **`sum_free_ge`, corrected for a cut free dimension.**  `sum_free_ge` needs
`dim − |C_k| ≤ Nfun k ω` everywhere; when `Nfun` is cut at a stopping time that fails after it, and
the repair is the extra term `dim·∑_k P(bad k)`.  Everything else is `sum_free_ge`'s own argument. -/
theorem sum_free_ge_cut (Cset : ℕ → Ω → Finset ι) (Nfun : ℕ → Ω → ℝ)
    (Good : ℕ → Set Ω) (dd : ℝ) (Nsteps : ℕ)
    (hfree : ∀ k, k < Nsteps → ∀ ω ∈ Good k, dd - ((Cset k ω).card : ℝ) ≤ Nfun k ω)
    (hzero : ∀ k, k < Nsteps → ∀ ω, 0 ≤ Nfun k ω)
    (_hdd : 0 ≤ dd)
    (hmeasG : ∀ k, MeasurableSet (Good k))
    (hintN : ∀ k, k < Nsteps → Integrable (Nfun k) μ)
    (hintC : ∀ k, k < Nsteps → Integrable (fun ω => ((Cset k ω).card : ℝ)) μ) :
    ∑ k ∈ Finset.range Nsteps,
        (dd - ∫ ω, ((Cset k ω).card : ℝ) ∂μ - dd * μ.real (Good k)ᶜ)
      ≤ ∑ k ∈ Finset.range Nsteps, ∫ ω, Nfun k ω ∂μ := by
  refine Finset.sum_le_sum fun k hk => ?_
  have hk' := Finset.mem_range.1 hk
  -- `Nfun k ≥ (dd - |C_k|) · 1_{Good k}` pointwise
  have hpt : ∀ ω, Set.indicator (Good k) (fun ω => dd - ((Cset k ω).card : ℝ)) ω ≤ Nfun k ω := by
    intro ω
    by_cases hg : ω ∈ Good k
    · rw [Set.indicator_of_mem hg]
      exact hfree k hk' ω hg
    · rw [Set.indicator_of_notMem hg]
      exact hzero k hk' ω
  have hintI : Integrable
      (Set.indicator (Good k) (fun ω => dd - ((Cset k ω).card : ℝ))) μ :=
    (((integrable_const dd).sub (hintC k hk')).indicator (hmeasG k))
  have hmono := integral_mono hintI (hintN k hk') hpt
  refine le_trans ?_ hmono
  -- `∫ 1_G (dd - |C|) ≥ dd - ∫|C| - dd·μ(Gᶜ)`
  have hintIc : Integrable (Set.indicator (Good k)ᶜ (fun ω => dd - ((Cset k ω).card : ℝ))) μ :=
    ((integrable_const dd).sub (hintC k hk')).indicator (hmeasG k).compl
  have hsum : ∀ ω, Set.indicator (Good k) (fun ω => dd - ((Cset k ω).card : ℝ)) ω
      + Set.indicator (Good k)ᶜ (fun ω => dd - ((Cset k ω).card : ℝ)) ω
      = dd - ((Cset k ω).card : ℝ) := by
    intro ω
    by_cases hg : ω ∈ Good k
    · rw [Set.indicator_of_mem hg, Set.indicator_of_notMem (by simpa using hg)]
      ring
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_mem (by simpa using hg)]
      ring
  have hadd : ∫ ω, (dd - ((Cset k ω).card : ℝ)) ∂μ
      = ∫ ω, Set.indicator (Good k) (fun ω => dd - ((Cset k ω).card : ℝ)) ω ∂μ
        + ∫ ω, Set.indicator (Good k)ᶜ (fun ω => dd - ((Cset k ω).card : ℝ)) ω ∂μ := by
    rw [← integral_add hintI hintIc]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => (hsum ω).symm)
  have hbd : ∫ ω, Set.indicator (Good k)ᶜ (fun ω => dd - ((Cset k ω).card : ℝ)) ω ∂μ
      ≤ dd * μ.real (Good k)ᶜ := by
    have hle : ∀ ω, Set.indicator (Good k)ᶜ (fun ω => dd - ((Cset k ω).card : ℝ)) ω
        ≤ Set.indicator (Good k)ᶜ (fun _ => dd) ω := by
      intro ω
      by_cases hg : ω ∈ (Good k)ᶜ
      · rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg]
        have hc : (0 : ℝ) ≤ ((Cset k ω).card : ℝ) := Nat.cast_nonneg _
        linarith
      · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg]
    have hmono2 := integral_mono hintIc ((integrable_const dd).indicator (hmeasG k).compl) hle
    rwa [integral_indicator_const dd (hmeasG k).compl, smul_eq_mul, mul_comm] at hmono2
  rw [integral_sub (integrable_const dd) (hintC k hk'), integral_const] at hadd
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul] at hadd
  linarith

end FreeDim

/-! ## 4. The gate, modulo brief 82a and brief 81 -/

section Final

variable {w : ∀ m : ℕ, ℝ → (Fin (m + 1) → ℤ) → ℝ≥0∞} {θ : ℕ → ℝ → ℝ≥0∞}

/-- **The gate on one hypothesis**, once brief 82a's `goodPath_of_S` lands: it is exactly the
statement that the light contact yields the good path, and §1–§3 are what it consumes. -/
theorem klartag_packing_final'' (hpr : Theorem2R.ParamsProducerR w θ)
    (hstep : LightGoodPath w θ 200000) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      let V := EuclideanSpace ℝ (Fin (n + 1))
      ∃ φ : V →ₗ[ℝ] V, let E := φ '' Metric.ball (0 : V) 1
        (MeasureTheory.volume E : EReal) = c * n ^ 2 ∧
        {v ∈ E | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} :=
  klartag_packing_final' hpr hstep

end Final

end Submission.L10.GoodPathLight

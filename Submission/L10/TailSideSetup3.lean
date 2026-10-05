import Submission.L10.TailSideSetup2
import Submission.L10.PaddedLawSetupR
import Submission.L10.LatticeDataR
import Submission.L10.RawDataInst2R

/-!
# Gate L-10 (`klartag_packing`), brief 78 — `TailSideHyp` without a window

Report 73's one blocker: `TailSideSetup2.tailSideHyp_of_rawData` is the **only** producer of
`TailSideHyp`, and it takes a `windowC`-shaped `RawData`, which `shellR` does not satisfy — neither
direction of implication holds between `RawData` and `RawDataR`, since `windowC ≤ windowR` makes
`supp_radius`/`hwin` weaker and `window_lt_p` stronger.

But that proof never looks at a window.  It reads exactly two fields, `hA₀` twice and `hr` once
(`PaddedLawSetupR.hA₀_and_hr` records it), and both are carried unchanged by `RawDataR`.  So the
fix is to restate it from those two hypotheses: `tailSideHyp_of_gap` below is
`TailSideSetup2.tailSideHyp_of_rawData`'s proof **verbatim**, with the three field reads replaced.
`TailSideSetup2` is reported and frozen, which is why this is a new module rather than an edit.

With the producer window-free, the three declarations report 73 left holding it as a hypothesis
close: `tailSideHyp_filterR'`, `tailSideHyp_latZR'`, and `hole52R` / `tailSideR`.
-/

set_option linter.unusedSectionVars false

namespace Submission.L10.TailSideSetup3

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal RealInnerProductSpace
open Submission.L10 Submission.L10.Increments Submission.L10.ChainSetup
open Submission.L10.PaddedLawSetup Submission.L10.TailSideSetup
open Submission.L10.TailSideSetup2 Submission.L10.PaddedLawSetupR
open Submission.L10.Tiling Submission.L10.Section5 Submission.L10.ConstructionA

noncomputable section

/-! ## 1. The window-free producer -/

/-- **`TailSideHyp` from the initial gap alone.**  `TailSideSetup2.tailSideHyp_of_rawData`'s proof
with `hraw.hA₀` and `hraw.hr` replaced by hypotheses — no window, and no new mathematics. -/
theorem tailSideHyp_of_gap {n : ℕ} {α : ℝ}
    {q : (Fin n → ℤ) → EuclideanSpace ℝ (UT n)} {W : Finset (Fin n → ℤ)}
    {A₀ : EuclideanSpace ℝ (UT n)}
    (hA₀ : ∀ y ∈ W, (1 : ℝ) < ⟪A₀, q y⟫) (hr : ∀ y ∈ W, 0 < α * ‖toE n y‖)
    (hnd : NormData n α q W A₀) (hn : 3 ≤ n) :
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
    have := hA₀ y hy
    rw [hz, inner_zero_right] at this
    linarith
  have hqn : (0 : ℝ) < ‖q y‖ := norm_pos_iff.2 hqy
  set u : ℝ := α * ‖toE n y‖ with hudef
  have hu0 : 0 < u := hr y hy
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
    have hgap := chain_hgap (q := q) (W := W) (A₀ := A₀) (ξ := step c) (hA₀ y hy)
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
/-- The old lane's producer, unchanged in meaning. -/
theorem tailSideHyp_of_rawData' {p n : ℕ} {α R : ℝ}
    {q : (Fin n → ℤ) → EuclideanSpace ℝ (UT n)} {W : Finset (Fin n → ℤ)}
    {A₀ : EuclideanSpace ℝ (UT n)}
    (hraw : RawData p n α R q W A₀) (hnd : NormData n α q W A₀) (hn : 3 ≤ n) :
    TailSideHyp n (Real.sqrt (ParamsAdopted2.stepSizeAdopted2 n)) α q W A₀ :=
  tailSideHyp_of_gap hraw.hA₀ hraw.hr hnd hn

/-- **The reach lane's producer** — this is what report 73 was missing. -/
theorem tailSideHyp_of_rawDataR {p n : ℕ} {α R : ℝ}
    {q : (Fin n → ℤ) → EuclideanSpace ℝ (UT n)} {W : Finset (Fin n → ℤ)}
    {A₀ : EuclideanSpace ℝ (UT n)}
    (hraw : RawDataR p n α R q W A₀) (hnd : NormData n α q W A₀) (hn : 3 ≤ n) :
    TailSideHypR n (Real.sqrt (ParamsAdopted2.stepSizeAdopted2 n)) α q W A₀ :=
  tailSideHyp_of_gap hraw.hA₀ hraw.hr hnd hn

/-! ## 2. The closing instances -/

/-- `LatticeDataR.tailSideHyp_filterR` with its `hprod` binder discharged. -/
theorem tailSideHyp_filterR' {p n : ℕ} {α R : ℝ}
    {q : (Fin n → ℤ) → EuclideanSpace ℝ (UT n)} {W : Finset (Fin n → ℤ)}
    {A₀ : EuclideanSpace ℝ (UT n)}
    (h : RawDataR p n α R q W A₀) (hnd : NormData n α q W A₀) (hn : 3 ≤ n)
    (P : (Fin n → ℤ) → Prop) [DecidablePred P] :
    TailSideHypR n (Real.sqrt (ParamsAdopted2.stepSizeAdopted2 n)) α q (W.filter P) A₀ :=
  LatticeDataR.tailSideHyp_filterR h hnd hn
    (fun _ h₁ hnd₁ => tailSideHyp_of_rawDataR h₁ hnd₁ hn) P

open Classical in
/-- The same at the drift side's lattice filter. -/
theorem tailSideHyp_latZR' {p n : ℕ} {α R : ℝ}
    {q : (Fin n → ℤ) → EuclideanSpace ℝ (UT n)} {W : Finset (Fin n → ℤ)}
    {A₀ : EuclideanSpace ℝ (UT n)}
    (h : RawDataR p n α R q W A₀) (hnd : NormData n α q W A₀) (hn : 3 ≤ n)
    (g : Fin n → ZMod p) :
    TailSideHypR n (Real.sqrt (ParamsAdopted2.stepSizeAdopted2 n)) α q
      (W.filter (fun y => y ∈ latZ p n g)) A₀ :=
  LatticeDataR.tailSideHyp_latZR h hnd hn
    (fun _ h₁ hnd₁ => tailSideHyp_of_rawDataR h₁ hnd₁ hn) g

/-- **HOLE 52 at the reach window, with no hypothesis.**  `RawDataInst2R.hole52R_of_tailSideHyp`
takes a producer whose binder does not carry `NormData`, so this goes through
`exists_rawData_normDataR` directly, which supplies both. -/
theorem hole52R :
    ∀ m : ℕ, Threshold2.n₁ ≤ m →
      ∃ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p) (c α R : ℝ)
        (q : (Fin (m + 1) → ℤ) → EuclideanSpace ℝ (UT (m + 1)))
        (W : Finset (Fin (m + 1) → ℤ)) (A₀ : EuclideanSpace ℝ (UT (m + 1))),
        3 ≤ m + 1 ∧ RawDataR p (m + 1) α R q W A₀ ∧ TailSideHypR (m + 1) c α q W A₀ := by
  intro m hm
  have hm' : 2073600 ≤ m := by simpa [Threshold2.n₁] using hm
  have h3 : 3 ≤ m + 1 := by omega
  obtain ⟨p, hp, hp0, α, R, q, W, A₀, hraw, hnd⟩ :=
    RawDataInst2R.exists_rawData_normDataR (n := m + 1) (by omega)
  exact ⟨p, hp, hp0, Real.sqrt (ParamsAdopted2.stepSizeAdopted2 (m + 1)), α, R, q, W, A₀,
    h3, hraw, tailSideHyp_of_rawDataR hraw hnd h3⟩

/-- **`PaddedLawSetupR.TailSideR`, with no hypothesis.** -/
theorem tailSideR : TailSideR := tailSide_on_setupR hole52R

end

end Submission.L10.TailSideSetup3

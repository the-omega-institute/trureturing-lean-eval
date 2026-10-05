import Mathlib
import Submission.L10.RawDataInst2
import Submission.L10.RawDataInstR

/-!
# Gate L-10 — the reach shell, and `RawDataR ∧ NormData` with no hypothesis

Brief 73, part 3.  `RawDataInst2` with `shell` replaced by `shellR` and `windowC` by `windowR`.

`shellR α n` is the integer points between Klartag's inner radius `(1−1/n)/α` (exclusive) and
`windowR α n − √n/2`, which is `WindowR.reachNum n / α` (`shellR_radius`) — the ellipsoid's reach,
report 68's correction to the window.  Since `windowC α n ≤ windowR α n`
(`WindowR.windowC_le_windowR`), `shell α n ⊆ shellR α n` (`shell_subset_shellR`).

`q`, `A₀` and `NormData` are **not** redefined: `RawDataInst2.qC`, `A0C` and `normData_qC` are
window-free and are reused verbatim.

**What is *not* here, and why.**  `hole52R` and `tailSideR` need `TailSideHyp` at `shellR`, and the
only producer in the tree is `TailSideSetup2.tailSideHyp_of_rawData`, which takes a full
`PaddedLawSetup.RawData` — i.e. the window fields at `windowC`, which `shellR` does not satisfy.
Its proof reads only `hraw.hA₀` and `hraw.hr` (grep over `TailSideSetup2.lean:158–225`), both of
which `RawDataR` carries unchanged, so a window-free restatement closes it; `TailSideSetup2` is
reported and frozen, so that restatement is a separate module.  `hole52R_of_tailSideHyp` below is
the hypothesis-taking form, exactly parallel to `RawDataInst.hole52_of_tailSideHyp`.
-/

set_option linter.unusedSectionVars false

namespace Submission.L10.RawDataInst2R

open MeasureTheory Finset
open scoped RealInnerProductSpace
open Submission.L10 Submission.L10.Section5 Submission.L10.Tiling
open Submission.L10.ConstructionA Submission.L10.PaddedLawSetup
open Submission.L10.Increments Submission.L10.ChainWiring Submission.L10.TailSideSetup2
open Submission.L10.RawDataInst Submission.L10.RawDataInst2
open Submission.L10.PaddedLawSetupR Submission.L10.RawDataInstR Submission.L10.WindowR

variable {n : ℕ}

/-! ### 1. The reach shell -/

open Classical in
/-- **The chain's window at the reach**: the integer points between `(1−1/n)/α` (exclusive) and
`windowR α n − √n/2` (inclusive). -/
noncomputable def shellR (α : ℝ) (n : ℕ) : Finset (Fin n → ℤ) :=
  ((Tiling.finite_ball_integer n (windowR α n - Real.sqrt n / 2)).toFinset).filter
    (fun y => (1 - 1 / (n : ℝ)) / α < ‖toE n y‖)

open Classical in
theorem mem_shellR {α : ℝ} {n : ℕ} {y : Fin n → ℤ} :
    y ∈ shellR α n ↔
      ‖toE n y‖ ≤ windowR α n - Real.sqrt n / 2 ∧ (1 - 1 / (n : ℝ)) / α < ‖toE n y‖ := by
  rw [shellR, Finset.mem_filter, Set.Finite.mem_toFinset]
  exact Iff.rfl

/-- The outer radius of the reach shell is `reachNum n / α`. -/
theorem shellR_radius (α : ℝ) (n : ℕ) :
    windowR α n - Real.sqrt n / 2 = reachNum n / α := by
  rw [windowR_eq]; ring

/-- **The old shell sits inside the new one.** -/
theorem shell_subset_shellR {α : ℝ} (hα : 0 < α) (hn : 2073600 ≤ n) :
    shell α n ⊆ shellR α n := by
  intro y hy
  rw [mem_shellR]
  refine ⟨?_, (mem_shell.1 hy).2⟩
  have h := (mem_shell.1 hy).1
  have := windowC_le_windowR (α := α) (n := n) hα hn
  linarith

/-! ### 2. The inner radius -/

/-- The inner radius, unscaled, on the reach shell. -/
theorem inner_radiusR {α : ℝ} (hα : 0 < α) {n : ℕ} {y : Fin n → ℤ} (hy : y ∈ shellR α n) :
    1 - 1 / (n : ℝ) < α * ‖toE n y‖ := by
  have h := (mem_shellR.1 hy).2
  rw [div_lt_iff₀ hα] at h
  linarith [h]

/-- `a₀·(α‖toE y‖)² > 1` from the inner radius alone — the window plays no part, so this serves
both lanes. -/
theorem a0C_mul_sq_gt_one_of_inner {α : ℝ} {n : ℕ} (hn : 2 ≤ n) {y : Fin n → ℤ}
    (hr : 1 - 1 / (n : ℝ) < α * ‖toE n y‖) : 1 < a0C n * (α * ‖toE n y‖) ^ 2 := by
  have hnr : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hb : (0 : ℝ) < 1 - 1 / (n : ℝ) := by
    have : 1 / (n : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hnr
    linarith
  have hsq : (1 - 1 / (n : ℝ)) ^ 2 < (α * ‖toE n y‖) ^ 2 := by nlinarith
  have hbb : (0 : ℝ) < (1 - 1 / (n : ℝ)) ^ 2 := by positivity
  rw [a0C, inv_pow, inv_mul_eq_div, lt_div_iff₀ hbb, one_mul]
  exact hsq

/-! ### 3. The seven lattice fields at the reach shell -/

/-- **The seven lattice fields**, for the chain's own `q`, `A₀` and the reach shell. -/
theorem lattice_fieldsR {α : ℝ} (hα : 0 < α) {n : ℕ} (hn : 3 ≤ n) :
    (∀ j : (Fin n → ℤ), ∀ i ∈ shellR α n, (0 : ℝ) ≤ ⟪qC α i, qC α j⟫) ∧
    (∀ y ∈ shellR α n, (1 : ℝ) < ⟪A0C n, qC α y⟫) ∧
    (∀ y ∈ shellR α n, y ≠ 0) ∧
    (∀ y ∈ shellR α n, ‖toE n y‖ ≤ windowR α n) ∧
    (∀ y ∈ shellR α n, ‖toE n y‖ + Real.sqrt n / 2 ≤ windowR α n) ∧
    (∀ y ∈ shellR α n, 0 < α * ‖toE n y‖) ∧
    (∀ k, k < ParamsAdopted2.numStepsAdopted2 n → k ≠ 0 → ∀ y ∈ shellR α n,
      0 < yOf (a0C n) ((k : ℝ) * ParamsAdopted2.stepSizeAdopted2 n) (α * ‖toE n y‖)) := by
  have hn2 : 2 ≤ n := by omega
  have hnr : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hb : (0 : ℝ) < 1 - 1 / (n : ℝ) := by
    have : 1 / (n : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hnr
    linarith
  have hpos : ∀ y ∈ shellR α n, 0 < α * ‖toE n y‖ := fun y hy =>
    lt_trans hb (inner_radiusR hα hy)
  refine ⟨fun j i _ => inner_qUT_nonneg _ _, fun y hy => ?_, fun y hy => ?_,
    fun y hy => ?_, fun y hy => ?_, hpos, ?_⟩
  · rw [inner_A0C_qC]
    exact a0C_mul_sq_gt_one_of_inner hn2 (inner_radiusR hα hy)
  · intro hzero
    have h0 : (0 : ℝ) < α * ‖toE n y‖ := hpos y hy
    have hz : ‖toE n y‖ = 0 := by
      rw [hzero, EuclideanSpace.norm_eq]
      simp [Tiling.toE_apply]
    rw [hz, mul_zero] at h0
    exact lt_irrefl 0 h0
  · have := (mem_shellR.1 hy).1
    have hs : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
    linarith
  · have := (mem_shellR.1 hy).1
    linarith
  · intro k hk hk0 y hy
    have ht : 0 < (k : ℝ) * ParamsAdopted2.stepSizeAdopted2 n := by
      have h1 : (0 : ℝ) < (k : ℝ) := by
        have : 0 < k := Nat.pos_of_ne_zero hk0
        exact_mod_cast this
      exact mul_pos h1 (TailSideSetup2.stepSizeAdopted2_pos hn)
    have hr0 : 0 < α * ‖toE n y‖ := hpos y hy
    have hgt := a0C_mul_sq_gt_one_of_inner hn2 (inner_radiusR hα hy)
    rw [yOf, div_pos_iff]
    left
    refine ⟨?_, Real.sqrt_pos.2 ht⟩
    rw [sub_pos, inv_lt_iff_one_lt_mul₀ (by positivity)]
    linarith [hgt]

/-! ### 4. `RawDataR ∧ NormData` with no hypothesis -/

/-- **`exists_rawDataR`, unconditional**: `RawDataR` *and* `NormData`, for the chain's own `q`,
`A₀` and the reach shell. -/
theorem exists_rawData_normDataR (hn : 2073600 ≤ n) :
    ∃ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p) (α R : ℝ)
      (q : (Fin n → ℤ) → EuclideanSpace ℝ (UT n)) (W : Finset (Fin n → ℤ))
      (A₀ : EuclideanSpace ℝ (UT n)),
      RawDataR p n α R q W A₀ ∧ NormData n α q W A₀ := by
  obtain ⟨p, hp, α, hαpos, hαnorm, hαsmall, hM⟩ :=
    exists_prime_alpha_mul (by omega : 2 ≤ n) (max (2 * reachNum n) (max 1 (Real.sqrt n)))
      (le_trans (le_max_left _ _) (le_max_right _ _))
  obtain ⟨hq, hA₀, hne0, hrad, hwin, hr, hy⟩ := lattice_fieldsR hαpos (by omega : 3 ≤ n)
  exact ⟨p, ⟨hp⟩, ⟨hp.ne_zero⟩, α, (1 - 1 / (n : ℝ)) / α, qC α, shellR α n, A0C n,
    rawData_of_latticeR hn hαpos hp.two_le hαnorm hαsmall hM hq hA₀ hne0 hrad hwin hr hy,
    normData_qC α (shellR α n)⟩

/-- **HOLE 52 at the reach window**, from the tail-side hypothesis.  The parallel of
`RawDataInst.hole52_of_tailSideHyp`; the unconditional form waits on a window-free restatement of
`TailSideSetup2.tailSideHyp_of_rawData` (see the module docstring). -/
theorem hole52R_of_tailSideHyp (c : ℝ)
    (htsh : ∀ (m p : ℕ) (α R : ℝ)
      (q : (Fin (m + 1) → ℤ) → EuclideanSpace ℝ (UT (m + 1)))
      (W : Finset (Fin (m + 1) → ℤ)) (A₀ : EuclideanSpace ℝ (UT (m + 1))),
      RawDataR p (m + 1) α R q W A₀ → 3 ≤ m + 1 → TailSideHypR (m + 1) c α q W A₀) :
    ∀ m : ℕ, Threshold2.n₁ ≤ m →
      ∃ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p) (c α R : ℝ)
        (q : (Fin (m + 1) → ℤ) → EuclideanSpace ℝ (UT (m + 1)))
        (W : Finset (Fin (m + 1) → ℤ)) (A₀ : EuclideanSpace ℝ (UT (m + 1))),
        3 ≤ m + 1 ∧ RawDataR p (m + 1) α R q W A₀ ∧ TailSideHypR (m + 1) c α q W A₀ := by
  intro m hm
  have hm' : 2073600 ≤ m := by simpa [Threshold2.n₁] using hm
  have h3 : 3 ≤ m + 1 := by omega
  obtain ⟨p, hp, hp0, α, R, q, W, A₀, hraw, _⟩ :=
    exists_rawData_normDataR (n := m + 1) (by omega)
  exact ⟨p, hp, hp0, c, α, R, q, W, A₀, h3, hraw, htsh m p α R q W A₀ hraw h3⟩

end Submission.L10.RawDataInst2R

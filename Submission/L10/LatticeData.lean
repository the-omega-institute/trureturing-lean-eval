import Submission.L10.RawDataInst2

/-!
# Gate L-10 (`klartag_packing`), brief 64 (re-scoped) — restriction, coverage, data-first existence

`RawDataInst2` already defines the chain's lattice data (`qC`, `A0C`, `shell`) and proves the seven
lattice fields, `NormData`, and `TailSide`.  Nothing here redefines any of it.  What is added is
what the **drift** side needs, which runs the chain not on the whole shell but on
`W_g := W.filter (· ∈ latZ p n g)` for its own good line `g`:

* `rawData_mono`, `normData_mono` — every field of `RawData` and of `NormData` is a `∀ y ∈ W`, so
  both restrict along `W' ⊆ W`;
* `tailSideHyp_filter` — hence brief 60's `TailSideHyp` holds on the filtered window, at the same
  scale `√(stepSizeAdopted2 n)`;
* `mem_shell_of_shell` — `RawDataInst2.mem_shell` in the form the drift side states the shell in,
  with the outer radius as `‖toE y‖ + √n/2 ≤ windowC α n`;
* `rawData_exists'` — `exists_rawData_normData` with the witnesses **named** (`qC α`,
  `shell α (m+1)`, `A0C (m+1)`) and `R = (1 − 1/n)/α` exposed, so a consumer can restrict them.
-/

set_option linter.unusedSectionVars false

namespace Submission.L10.LatticeData

open MeasureTheory Finset
open scoped RealInnerProductSpace
open Submission.L10 Submission.L10.Section5 Submission.L10.Tiling
open Submission.L10.ConstructionA Submission.L10.PaddedLawSetup
open Submission.L10.Increments Submission.L10.ChainWiring Submission.L10.TailSideSetup2
open Submission.L10.RawDataInst Submission.L10.RawDataInst2

noncomputable section

/-! ## 1. Restriction to a sub-window -/

section Restrict

variable {n p : ℕ} {α R : ℝ} {q : (Fin n → ℤ) → EuclideanSpace ℝ (UT n)}
  {W W' : Finset (Fin n → ℤ)} {A₀ : EuclideanSpace ℝ (UT n)}

/-- **`RawData` restricts.**  Every field is either `∀ y ∈ W` or independent of `W`. -/
theorem rawData_mono (h : RawData p n α R q W A₀) (hsub : W' ⊆ W) :
    RawData p n α R q W' A₀ :=
  { hq := fun j i hi => h.hq j i (hsub hi)
    hA₀ := fun y hy => h.hA₀ y (hsub hy)
    alpha_pos := h.alpha_pos
    alpha_norm := h.alpha_norm
    R_nonneg := h.R_nonneg
    R_scaled := h.R_scaled
    R_lt_p := h.R_lt_p
    tiling_defect := h.tiling_defect
    window_lt_p := h.window_lt_p
    supp_ne_zero := fun y hy => h.supp_ne_zero y (hsub hy)
    supp_radius := fun y hy => h.supp_radius y (hsub hy)
    hwin := fun y hy => h.hwin y (hsub hy)
    hr := fun y hy => h.hr y (hsub hy)
    hy := fun k hk hk0 y hy => h.hy k hk hk0 y (hsub hy)
    arith := h.arith }

/-- **`NormData` restricts.** -/
theorem normData_mono (h : NormData n α q W A₀) (hsub : W' ⊆ W) : NormData n α q W' A₀ :=
  ⟨fun y hy => h.hnorm y (hsub hy), fun y hy => h.hinner y (hsub hy)⟩

/-- **`TailSideHyp` on the drift side's window** `W_g = W.filter (· ∈ latZ p n g)`, at brief 60's
scale. -/
theorem tailSideHyp_filter (h : RawData p n α R q W A₀) (hnd : NormData n α q W A₀)
    (hn : 3 ≤ n) (P : (Fin n → ℤ) → Prop) [DecidablePred P] :
    TailSideHyp n (Real.sqrt (ParamsAdopted2.stepSizeAdopted2 n)) α q (W.filter P) A₀ :=
  TailSideSetup2.tailSideHyp_of_rawData (rawData_mono h (Finset.filter_subset _ _))
    (normData_mono hnd (Finset.filter_subset _ _)) hn

open Classical in
/-- The same at the lattice filter the drift side actually uses. -/
theorem tailSideHyp_latZ (h : RawData p n α R q W A₀) (hnd : NormData n α q W A₀)
    (hn : 3 ≤ n) (g : Fin n → ZMod p) :
    TailSideHyp n (Real.sqrt (ParamsAdopted2.stepSizeAdopted2 n)) α q
      (W.filter (fun y => y ∈ latZ p n g)) A₀ :=
  tailSideHyp_filter h hnd hn _

end Restrict

/-! ## 2. Coverage, in the drift side's shape -/

section Coverage

variable {n : ℕ} {α : ℝ}

/-- **Coverage.**  `RawDataInst2.mem_shell` with the outer radius written additively — the form the
drift side's avoidance argument states the shell in. -/
theorem mem_shell_of_shell {y : Fin n → ℤ} (_h0 : y ≠ 0)
    (hin : (1 - 1 / (n : ℝ)) / α < ‖toE n y‖)
    (hout : ‖toE n y‖ + Real.sqrt n / 2 ≤ windowC α n) : y ∈ shell α n :=
  mem_shell.2 ⟨by linarith, hin⟩

end Coverage

/-! ## 3. The tail side's data, with the witnesses named -/

section Exists

/-- **`RawData`, `NormData` and coverage at every dimension above the threshold, with no
hypothesis and with the witnesses named.**  `RawDataInst2.exists_rawData_normData` hides `q`, `W`
and `A₀` behind existentials, which a consumer that has to *restrict* the window cannot use; this
exposes them, together with `R = (1 − 1/n)/α`. -/
theorem rawData_exists' (m : ℕ) (hm : Threshold2.n₁ ≤ m) :
    ∃ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p) (α : ℝ), 0 < α ∧ 3 ≤ m + 1 ∧
      RawData p (m + 1) α ((1 - 1 / ((m + 1 : ℕ) : ℝ)) / α)
          (qC α) (shell α (m + 1)) (A0C (m + 1)) ∧
      NormData (m + 1) α (qC α) (shell α (m + 1)) (A0C (m + 1)) ∧
      (∀ y : Fin (m + 1) → ℤ, y ≠ 0 →
        (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α < ‖toE (m + 1) y‖ →
        ‖toE (m + 1) y‖ + Real.sqrt ((m + 1 : ℕ) : ℝ) / 2 ≤ windowC α (m + 1) →
          y ∈ shell α (m + 1)) := by
  have h3 : 3 ≤ m + 1 := by
    have : 2073600 ≤ m := by simpa [Threshold2.n₁] using hm
    omega
  obtain ⟨p, hp, α, hαpos, hαnorm, hαsmall, hM⟩ :=
    exists_prime_alpha_mul (by omega : 2 ≤ m + 1)
      (max (2 * winNum (m + 1)) (max 1 (Real.sqrt ((m + 1 : ℕ) : ℝ))))
      (le_trans (le_max_left _ _) (le_max_right _ _))
  obtain ⟨hq, hA₀, hne0, hrad, hwin, hr, hy⟩ := lattice_fields hαpos h3
  exact ⟨p, ⟨hp⟩, ⟨hp.ne_zero⟩, α, hαpos, h3,
    rawData_of_lattice (by omega) hαpos hp.two_le hαnorm hαsmall hM hq hA₀ hne0 hrad hwin hr hy,
    normData_qC α (shell α (m + 1)),
    fun y h0 hin hout => mem_shell_of_shell h0 hin hout⟩

end Exists

end

end Submission.L10.LatticeData

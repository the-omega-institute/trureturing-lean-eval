import Mathlib
import Submission.L10.LatticeData
import Submission.L10.RawDataInst2R

/-!
# Gate L-10 — the reach lane's restriction, coverage, and data-first existence

Brief 73, part 4.  `LatticeData` with `RawData → RawDataR`, `shell → shellR`,
`windowC → windowR`.

`rawData_monoR` is `PaddedLawSetupR.rawDataR_mono`, re-exported under the name the brief asks for;
`normData_mono` is window-free and is `LatticeData.normData_mono`, reused unchanged.

`tailSideHyp_latZR` is **not** unconditional here, for the reason `RawDataInst2R`'s docstring gives:
the only `TailSideHyp` producer takes a `windowC`-shaped `RawData`.  `tailSideHyp_filterR` and
`tailSideHyp_latZR` below take that producer as a hypothesis and do the restriction, which is the
whole of what `LatticeData.tailSideHyp_filter` adds on top of it.
-/

set_option linter.unusedSectionVars false

namespace Submission.L10.LatticeDataR

open MeasureTheory Finset
open scoped RealInnerProductSpace
open Submission.L10 Submission.L10.Section5 Submission.L10.Tiling
open Submission.L10.ConstructionA Submission.L10.PaddedLawSetup
open Submission.L10.Increments Submission.L10.ChainWiring Submission.L10.TailSideSetup2
open Submission.L10.RawDataInst Submission.L10.RawDataInst2
open Submission.L10.PaddedLawSetupR Submission.L10.RawDataInstR Submission.L10.RawDataInst2R
open Submission.L10.WindowR

noncomputable section

/-! ## 1. Restriction -/

section Restrict

variable {n p : ℕ} {α R : ℝ} {q : (Fin n → ℤ) → EuclideanSpace ℝ (UT n)}
  {W W' : Finset (Fin n → ℤ)} {A₀ : EuclideanSpace ℝ (UT n)}

/-- **`RawDataR` restricts** — `PaddedLawSetupR.rawDataR_mono` under the brief's name. -/
theorem rawData_monoR (h : RawDataR p n α R q W A₀) (hsub : W' ⊆ W) :
    RawDataR p n α R q W' A₀ := rawDataR_mono h hsub

/-- **`TailSideHyp` on a restricted window**, given a producer at the full window.  The producer
is a hypothesis because `TailSideSetup2.tailSideHyp_of_rawData` demands a `windowC`-shaped
`RawData`; everything else is `LatticeData.tailSideHyp_filter`'s content. -/
theorem tailSideHyp_filterR {c : ℝ} (h : RawDataR p n α R q W A₀) (hnd : NormData n α q W A₀)
    (_hn : 3 ≤ n)
    (hprod : ∀ W₁ : Finset (Fin n → ℤ), RawDataR p n α R q W₁ A₀ → NormData n α q W₁ A₀ →
      TailSideHypR n c α q W₁ A₀)
    (P : (Fin n → ℤ) → Prop) [DecidablePred P] :
    TailSideHypR n c α q (W.filter P) A₀ :=
  hprod _ (rawData_monoR h (Finset.filter_subset _ _))
    (LatticeData.normData_mono hnd (Finset.filter_subset _ _))

open Classical in
/-- The same at the lattice filter the drift side uses. -/
theorem tailSideHyp_latZR {c : ℝ} (h : RawDataR p n α R q W A₀) (hnd : NormData n α q W A₀)
    (hn : 3 ≤ n)
    (hprod : ∀ W₁ : Finset (Fin n → ℤ), RawDataR p n α R q W₁ A₀ → NormData n α q W₁ A₀ →
      TailSideHypR n c α q W₁ A₀)
    (g : Fin n → ZMod p) :
    TailSideHypR n c α q (W.filter (fun y => y ∈ latZ p n g)) A₀ :=
  tailSideHyp_filterR h hnd hn hprod _

end Restrict

/-! ## 2. Coverage -/

section Coverage

variable {n : ℕ} {α : ℝ}

/-- **Coverage at the reach window**, with the outer radius written additively. -/
theorem mem_shellR_of_shell {y : Fin n → ℤ} (_h0 : y ≠ 0)
    (hin : (1 - 1 / (n : ℝ)) / α < ‖toE n y‖)
    (hout : ‖toE n y‖ + Real.sqrt n / 2 ≤ windowR α n) : y ∈ shellR α n :=
  mem_shellR.2 ⟨by linarith, hin⟩

end Coverage

/-! ## 3. The tail side's data, with the witnesses named -/

section Exists

/-- **`RawDataR`, `NormData` and coverage at every dimension above the threshold**, with no
hypothesis and with `q`, `W`, `A₀` and `R` named. -/
theorem rawData_exists'R (m : ℕ) (hm : Threshold2.n₁ ≤ m) :
    ∃ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p) (α : ℝ), 0 < α ∧ 3 ≤ m + 1 ∧
      RawDataR p (m + 1) α ((1 - 1 / ((m + 1 : ℕ) : ℝ)) / α)
          (qC α) (shellR α (m + 1)) (A0C (m + 1)) ∧
      NormData (m + 1) α (qC α) (shellR α (m + 1)) (A0C (m + 1)) ∧
      (∀ y : Fin (m + 1) → ℤ, y ≠ 0 →
        (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α < ‖toE (m + 1) y‖ →
        ‖toE (m + 1) y‖ + Real.sqrt ((m + 1 : ℕ) : ℝ) / 2 ≤ windowR α (m + 1) →
          y ∈ shellR α (m + 1)) := by
  have hm' : 2073600 ≤ m := by simpa [Threshold2.n₁] using hm
  have h3 : 3 ≤ m + 1 := by omega
  obtain ⟨p, hp, α, hαpos, hαnorm, hαsmall, hM⟩ :=
    exists_prime_alpha_mul (by omega : 2 ≤ m + 1)
      (max (2 * reachNum (m + 1)) (max 1 (Real.sqrt ((m + 1 : ℕ) : ℝ))))
      (le_trans (le_max_left _ _) (le_max_right _ _))
  obtain ⟨hq, hA₀, hne0, hrad, hwin, hr, hy⟩ := lattice_fieldsR hαpos h3
  exact ⟨p, ⟨hp⟩, ⟨hp.ne_zero⟩, α, hαpos, h3,
    rawData_of_latticeR (by omega) hαpos hp.two_le hαnorm hαsmall hM hq hA₀ hne0 hrad hwin hr hy,
    normData_qC α (shellR α (m + 1)),
    fun y h0 hin hout => mem_shellR_of_shell h0 hin hout⟩

end Exists

end

end Submission.L10.LatticeDataR

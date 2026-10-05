import Submission.L10.DriftStopped8
import Submission.L10.Theorem4R

/-!
# Gate L-10 — the band closes at the reach window

Brief 73, addition.  `DriftStopped8` with `windowC → windowR`, `shell → shellR`, and the
light-contact clause carrying a **parameterised weight and threshold** (report 74: the count event
needs a terminal-count weight distinct from the time-integrated one, and §4 there combines them
into a single `w' = c·w_int + c_T·w_T` before §5's selection, so one `LightContact` with an
abstract `w` is the right shape to state now and specialise once `w'` exists).

`Theorem4R.lean` is reported and frozen (rule 5), so the re-parameterised statement lives here as
`DriftSideW`; `Theorem4R.DriftSide''''` is the same predicate with `w` and `θ` already pinned to
`chainWR` and an abstract `θ`.

**The band is a theorem here, not a hypothesis.**  `WindowR.windowR α n − √n/2 = reachNum n/α`
(`RawDataInst2R.shellR_radius`) and `WindowR.reachNum_eq : reachNum n = 1/√(mR n)` with
`WindowR.mR n = DriftStopped6.mAdopted n` by definition, so a lattice point beyond the reach
window is beyond the reach — which is exactly `BandHypR`.  That is what moving the window out
was for.

**One correction to the assignment.**  `BandSideAdoptedR` was specified as `∀ p α g`, with no
sign condition on `α`.  That statement is **false**: at `α < 0` the hypothesis
`windowR α n − √n/2 < ‖toE y‖` reads `reachNum n/α < ‖toE y‖`, which holds for every `y` since the
left side is negative, while the conclusion `1/√mLow ≤ α‖toE y‖` has a non-positive right side; at
`α = 0` the same happens with `reachNum n/0 = 0`.  `0 < α` is added below, and every consumer has
it (`DriftStopped8.driftSide'''_of_obligation_of_band` calls the band under `hα`).
-/

set_option linter.unusedSectionVars false

namespace Submission.L10.DriftStopped8R

open MeasureTheory Matrix Finset Module Submission.L10 Submission.L10.Increments
open Submission.L10.ConstructionA Submission.L10.Tiling Submission.L10.PaddedLawSetup
open Submission.L10.TailSideSetup2 Submission.L10.RawDataInst2 Submission.L10.Theorem2
open Submission.L10.DriftStopped7 Submission.L10.DriftStopped8
open Submission.L10.PaddedLawSetupR Submission.L10.RawDataInst2R
open Submission.L10.LatticeDataR Submission.L10.Theorem4R Submission.L10.WindowR
open scoped ENNReal RealInnerProductSpace

variable {n m p : ℕ}

/-! ## 1. The drift side's window at the reach -/

open Classical in
/-- `W_g` at the reach window. -/
noncomputable def windowOfR (α : ℝ) (p m : ℕ) (g : Fin (m + 1) → ZMod p) :
    Finset (Fin (m + 1) → ℤ) :=
  (shellR α (m + 1)).filter (fun y => y ∈ latZ p (m + 1) g)

theorem mem_windowOfR {p m : ℕ} {α : ℝ} {g : Fin (m + 1) → ZMod p} {y : Fin (m + 1) → ℤ} :
    y ∈ windowOfR α p m g ↔ y ∈ shellR α (m + 1) ∧ y ∈ latZ p (m + 1) g := by
  classical
  rw [windowOfR, Finset.mem_filter]

open Classical in
/-- Rule 16: any other `open Classical` filter of the same predicate is this `Finset`. -/
theorem filter_eq_windowOfR {p m : ℕ} {α : ℝ} {g : Fin (m + 1) → ZMod p}
    [DecidablePred (fun y : Fin (m + 1) → ℤ => y ∈ latZ p (m + 1) g)] :
    (shellR α (m + 1)).filter (fun y => y ∈ latZ p (m + 1) g) = windowOfR α p m g := by
  ext y
  rw [Finset.mem_filter, mem_windowOfR]

/-! ## 2. The band, at the reach -/

/-- **`DriftStopped8.BandHyp` at the reach window.** -/
def BandHypR (p m : ℕ) (α mLow : ℝ) (g : Fin (m + 1) → ZMod p) : Prop :=
  ∀ y : Fin (m + 1) → ℤ, y ≠ 0 → y ∈ latZ p (m + 1) g →
    windowR α (m + 1) - Real.sqrt ((m + 1 : ℕ) : ℝ) / 2 < ‖toE (m + 1) y‖ →
    1 / Real.sqrt mLow ≤ α * ‖toE (m + 1) y‖

/-- **The band at the reach window is trivial** — that is the whole point of report 68's move. -/
theorem bandHypR_of_pos {α : ℝ} (hα : 0 < α) (hm : 2073600 ≤ m + 1)
    (g : Fin (m + 1) → ZMod p) : BandHypR p m α (DriftStopped6.mAdopted (m + 1)) g := by
  intro y _hy0 _hylat hfar
  rw [shellR_radius] at hfar
  have h1 : reachNum (m + 1) < α * ‖toE (m + 1) y‖ := by
    rw [div_lt_iff₀ hα] at hfar; linarith
  have h2 : reachNum (m + 1) = 1 / Real.sqrt (mR (m + 1)) := reachNum_eq hm
  rw [h2] at h1
  exact le_of_lt h1

/-- The band, hoisted, at the adopted lower bound.  `0 < α` is the correction the module docstring
records. -/
def BandSideAdoptedR : Prop :=
  ∀ m : ℕ, Threshold2.n₁ ≤ m → ∀ (p : ℕ) (α : ℝ), 0 < α → ∀ (g : Fin (m + 1) → ZMod p),
    BandHypR p m α (DriftStopped6.mAdopted (m + 1)) g

/-- **`BandSideAdoptedR` is a theorem.** -/
theorem bandSideAdoptedR : BandSideAdoptedR := by
  intro m hm p α hα g
  have hm' : 2073600 ≤ m := by simpa [Threshold2.n₁] using hm
  exact bandHypR_of_pos hα (by omega) g

/-! ## 3. The three cases at the reach window -/

/-- **`DriftStopped8.avoid_of_cases` at the reach window.**  The proof is the same three-case
split; only the window names change. -/
theorem avoid_of_casesR {α : ℝ} (hα : 0 < α) {g : Fin (m + 1) → ZMod p}
    {A : EuclideanSpace ℝ (UT (m + 1))} {mLow M : ℝ}
    (hSB : Discharge.StateBounds (symMat A) mLow M)
    (hkSet : A ∈ Chain.kSet (qC α) (windowOfR α p m g))
    (hcov : ∀ y : Fin (m + 1) → ℤ, y ≠ 0 →
      (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α < ‖toE (m + 1) y‖ →
      ‖toE (m + 1) y‖ + Real.sqrt ((m + 1 : ℕ) : ℝ) / 2 ≤ windowR α (m + 1) →
        y ∈ shellR α (m + 1))
    (hfree : ∀ y : Fin (m + 1) → ℤ, y ≠ 0 →
      ‖toE (m + 1) y‖ ≤ (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α → y ∉ latZ p (m + 1) g)
    (hband : BandHypR p m α mLow g) :
    ∀ y : Fin (m + 1) → ℤ, y ≠ 0 → y ∈ latZ p (m + 1) g →
      (WithLp.toLp 2 (xOf α y) : EuclideanSpace ℝ (Fin (m + 1)))
        ∉ ChainEllipsoid.ellipsoid (symMat A) := by
  intro y hy0 hylat
  by_cases hshort : ‖toE (m + 1) y‖ ≤ (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α
  · exact absurd hylat (hfree y hy0 hshort)
  have hlong : (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α < ‖toE (m + 1) y‖ := not_le.1 hshort
  by_cases hin : ‖toE (m + 1) y‖ + Real.sqrt ((m + 1 : ℕ) : ℝ) / 2 ≤ windowR α (m + 1)
  · exact notMem_ellipsoid_of_mem_kSet hkSet (mem_windowOfR.2 ⟨hcov y hy0 hlong hin, hylat⟩)
  · have hfar : windowR α (m + 1) - Real.sqrt ((m + 1 : ℕ) : ℝ) / 2 < ‖toE (m + 1) y‖ := by
      have hgt := not_le.1 hin
      linarith
    have hreach := hband y hy0 hylat hfar
    rw [← norm_toLp_xOf hα.le y] at hreach
    exact notMem_ellipsoid_of_reach hSB hreach

/-! ## 4. The drift side at the reach window -/

/-- **`Theorem4R.DriftSide''''` with the light-contact weight and threshold abstract.** -/
def DriftSideW (w : ∀ m : ℕ, ℝ → (Fin (m + 1) → ℤ) → ℝ≥0∞) (θ : ℕ → ℝ → ℝ≥0∞) (c₀ : ℝ) : Prop :=
  ∀ m : ℕ, Threshold2.n₁ ≤ m → ∀ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p) (α : ℝ),
    0 < α → ∀ (_hn : 3 ≤ m + 1)
      (_hraw : RawDataR p (m + 1) α ((1 - 1 / ((m + 1 : ℕ) : ℝ)) / α)
        (qC α) (shellR α (m + 1)) (A0C (m + 1)))
      (_hnd : NormData (m + 1) α (qC α) (shellR α (m + 1)) (A0C (m + 1))),
      (∀ y : Fin (m + 1) → ℤ, y ≠ 0 →
        (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α < ‖toE (m + 1) y‖ →
        ‖toE (m + 1) y‖ + Real.sqrt ((m + 1 : ℕ) : ℝ) / 2 ≤ windowR α (m + 1) →
          y ∈ shellR α (m + 1)) →
      ∀ (g : Fin (m + 1) → ZMod p), g ≠ 0 →
      (∀ y : Fin (m + 1) → ℤ, y ≠ 0 →
        ‖toE (m + 1) y‖ ≤ (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α → y ∉ latZ p (m + 1) g) →
      LightContact (w m α) (shellR α (m + 1)) (θ m α) g →
      Assembly.ChainOutput α g c₀

/-- **The state supply at the reach window**, with `mLow` fixed at the adopted lower bound and the
band removed — `bandSideAdoptedR` supplies it. -/
def StateSupplyAdoptedR (w : ∀ m : ℕ, ℝ → (Fin (m + 1) → ℤ) → ℝ≥0∞) (θ : ℕ → ℝ → ℝ≥0∞)
    (C' : ℝ) : Prop :=
  ∀ m : ℕ, Threshold2.n₁ ≤ m → ∀ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p) (α : ℝ),
    0 < α → ∀ (_hn : 3 ≤ m + 1)
      (_hraw : RawDataR p (m + 1) α ((1 - 1 / ((m + 1 : ℕ) : ℝ)) / α)
        (qC α) (shellR α (m + 1)) (A0C (m + 1)))
      (_hnd : NormData (m + 1) α (qC α) (shellR α (m + 1)) (A0C (m + 1))),
      (∀ y : Fin (m + 1) → ℤ, y ≠ 0 →
        (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α < ‖toE (m + 1) y‖ →
        ‖toE (m + 1) y‖ + Real.sqrt ((m + 1 : ℕ) : ℝ) / 2 ≤ windowR α (m + 1) →
          y ∈ shellR α (m + 1)) →
      ∀ (g : Fin (m + 1) → ZMod p), g ≠ 0 →
      (∀ y : Fin (m + 1) → ℤ, y ≠ 0 →
        ‖toE (m + 1) y‖ ≤ (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α → y ∉ latZ p (m + 1) g) →
      LightContact (w m α) (shellR α (m + 1)) (θ m α) g →
      ∃ (A : EuclideanSpace ℝ (UT (m + 1))) (M : ℝ),
        A ∈ Chain.kSet (qC α) (windowOfR α p m g) ∧
        Discharge.StateBounds (symMat A) (DriftStopped6.mAdopted (m + 1)) M ∧
        ChainWiring.logDet A ≤ C' - 4 * Real.log ((m + 1 : ℕ) : ℝ)

/-- **Goal (5) at the reach window, with the band discharged.**  `c₀ = exp(−C'/2)`, produced. -/
theorem driftSide''''_of_stateSupplyR
    {w : ∀ m : ℕ, ℝ → (Fin (m + 1) → ℤ) → ℝ≥0∞} {θ : ℕ → ℝ → ℝ≥0∞} {C' : ℝ}
    (h : StateSupplyAdoptedR w θ C') :
    ∃ c₀ : ℝ, 0 < c₀ ∧ DriftSideW w θ c₀ := by
  refine ⟨Real.exp (-C' / 2), Real.exp_pos _, ?_⟩
  intro m hm p hp hp0 α hα hn hraw hnd hcov g hg hfree hlight
  obtain ⟨A, M, hkSet, hSB, hlog⟩ := h m hm p hp hp0 α hα hn hraw hnd hcov g hg hfree hlight
  have hm0 : m ≠ 0 := by
    have h2 : 2073600 ≤ m := by simpa [Threshold2.n₁] using hm
    omega
  exact chainOutput_of_state hm0 hSB hlog
    (avoid_of_casesR hα hSB hkSet hcov hfree (bandSideAdoptedR m hm p α hα g))

end Submission.L10.DriftStopped8R

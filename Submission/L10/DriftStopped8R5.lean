import Submission.L10.WindowR2
import Submission.L10.DriftStopped8R3
import Submission.L10.LatticeDataRW2

/-!
# Gate L-10 — the band at the generic reach window `windowR2`, for every admissible `c₃`

Brief 85c.  Report 82a: `GoodPath` at `c₃ = n²` is unsatisfiable, and the repair moves the
contact threshold to `c₃'` and the state's lower eigenvalue bound from `DriftStopped6.mAdopted`
to `GoodPathBounds.mAt (m+1) c₃'`.  Because `mAt n c₃` **decreases** in `c₃`, the reach grows with
it, and the old window would stop covering it — which is why 85a re-based the window generically
at `mR2 n = a0C n − 1/2`.

`bandSideAdoptedR2` below is the payoff: at `windowR2` the band closes **for every `c₃` admissible
under `c₃·η ≤ 1/4`**, not just for one adopted value, so the count-threshold repair cannot reopen
it.  It is stated generically in `c₃` (rule 14) and specialises to `c3Adopted'` when
`DriftStopped6b` lands.
-/

set_option linter.unusedSectionVars false

namespace Submission.L10.DriftStopped8R5

open MeasureTheory Matrix Finset Module Submission.L10 Submission.L10.Increments
open Submission.L10.ConstructionA Submission.L10.Tiling
open Submission.L10.WindowR2 Submission.L10.GoodPathBounds Submission.L10.RawDataInst2
open scoped ENNReal RealInnerProductSpace

variable {m p : ℕ}

/-- **`DriftStopped8R.BandHypR` at the generic reach window.** -/
def BandHypR2 (p m : ℕ) (α mLow : ℝ) (g : Fin (m + 1) → ZMod p) : Prop :=
  ∀ y : Fin (m + 1) → ℤ, y ≠ 0 → y ∈ latZ p (m + 1) g →
    windowR2 α (m + 1) - Real.sqrt ((m + 1 : ℕ) : ℝ) / 2 < ‖toE (m + 1) y‖ →
    1 / Real.sqrt mLow ≤ α * ‖toE (m + 1) y‖

/-- The outer radius of the generic reach window. -/
theorem windowR2_sub (α : ℝ) (n : ℕ) :
    windowR2 α n - Real.sqrt n / 2 = reachNum2 n / α := by
  rw [windowR2_eq]; ring

/-- **The band at `windowR2`, for every admissible `c₃`.**  `mAt n c₃ ≥ mR2 n` (85a's
`mAt_ge_mR2`) and `reachNum2 n = 1/√(mR2 n)`, so a lattice point beyond the window is beyond the
reach of *any* state with lower bound `mAt n c₃`. -/
theorem bandHypR2_of_pos {α : ℝ} (hα : 0 < α) (hm : 2073600 ≤ m + 1) {c₃ : ℝ}
    (hc₃0 : 0 ≤ c₃) (hc₃ : c₃ * DriftStopped6.etaAdopted (m + 1) ≤ 1 / 4)
    (g : Fin (m + 1) → ZMod p) : BandHypR2 p m α (mAt (m + 1) c₃) g := by
  intro y _hy0 _hylat hfar
  rw [windowR2_sub] at hfar
  have hlt : reachNum2 (m + 1) < α * ‖toE (m + 1) y‖ := by
    rw [div_lt_iff₀ hα] at hfar; linarith
  have hmR2 : 0 < mR2 (m + 1) := mR2_pos hm
  have hge : mR2 (m + 1) ≤ mAt (m + 1) c₃ := mAt_ge_mR2 hm hc₃0 hc₃
  have hs : Real.sqrt (mR2 (m + 1)) ≤ Real.sqrt (mAt (m + 1) c₃) := Real.sqrt_le_sqrt hge
  have hs0 : 0 < Real.sqrt (mR2 (m + 1)) := Real.sqrt_pos.2 hmR2
  have hinv : 1 / Real.sqrt (mAt (m + 1) c₃) ≤ 1 / Real.sqrt (mR2 (m + 1)) :=
    one_div_le_one_div_of_le hs0 hs
  rw [reachNum2_eq hm] at hlt
  linarith

/-- The band hoisted over all dimensions and lines, generically in `c₃`.  `0 < α` is required —
report 73b §1 showed the version without it is false. -/
def BandSideAdoptedR2 (c₃ : ℕ → ℝ) : Prop :=
  ∀ m : ℕ, Threshold2.n₁ ≤ m → ∀ (p : ℕ) (α : ℝ), 0 < α → ∀ (g : Fin (m + 1) → ZMod p),
    BandHypR2 p m α (mAt (m + 1) (c₃ (m + 1))) g

/-- **`BandSideAdoptedR2` is a theorem** for every admissible threshold family. -/
theorem bandSideAdoptedR2 {c₃ : ℕ → ℝ} (hc₃0 : ∀ n, 0 ≤ c₃ n)
    (hc₃ : ∀ n, c₃ n * DriftStopped6.etaAdopted n ≤ 1 / 4) : BandSideAdoptedR2 c₃ := by
  intro m hm p α hα g
  have hm' : 2073600 ≤ m := by simpa [Threshold2.n₁] using hm
  exact bandHypR2_of_pos hα (by omega) (hc₃0 (m + 1)) (hc₃ (m + 1)) g

/-! ## 2. The drift side's window at the generic reach -/

open Classical in
/-- `W_g` at the generic reach window, over 85b's `RawDataInst2RW2.shellR`. -/
noncomputable def windowOfR2 (α : ℝ) (p m : ℕ) (g : Fin (m + 1) → ZMod p) :
    Finset (Fin (m + 1) → ℤ) :=
  (RawDataInst2RW2.shellR α (m + 1)).filter (fun y => y ∈ latZ p (m + 1) g)

theorem mem_windowOfR2 {p m : ℕ} {α : ℝ} {g : Fin (m + 1) → ZMod p} {y : Fin (m + 1) → ℤ} :
    y ∈ windowOfR2 α p m g ↔
      y ∈ RawDataInst2RW2.shellR α (m + 1) ∧ y ∈ latZ p (m + 1) g := by
  classical
  rw [windowOfR2, Finset.mem_filter]

theorem windowOfR2_subset {p m : ℕ} {α : ℝ} {g : Fin (m + 1) → ZMod p} :
    windowOfR2 α p m g ⊆ RawDataInst2RW2.shellR α (m + 1) :=
  fun _y hy => (mem_windowOfR2.1 hy).1

open Classical in
/-- Rule 16: any other `open Classical` filter of the same predicate is this `Finset`. -/
theorem filter_eq_windowOfR2 {p m : ℕ} {α : ℝ} {g : Fin (m + 1) → ZMod p}
    [DecidablePred (fun y : Fin (m + 1) → ℤ => y ∈ latZ p (m + 1) g)] :
    (RawDataInst2RW2.shellR α (m + 1)).filter (fun y => y ∈ latZ p (m + 1) g)
      = windowOfR2 α p m g := by
  ext y
  rw [Finset.mem_filter, mem_windowOfR2]

/-! ## 3. The three cases at the generic reach window -/

/-- **`DriftStopped8.avoid_of_cases` at `windowR2`.** -/
theorem avoid_of_casesR2 {α : ℝ} (hα : 0 < α) {g : Fin (m + 1) → ZMod p}
    {A : EuclideanSpace ℝ (UT (m + 1))} {mLow M : ℝ}
    (hSB : Discharge.StateBounds (symMat A) mLow M)
    (hkSet : A ∈ Chain.kSet (qC α) (windowOfR2 α p m g))
    (hcov : ∀ y : Fin (m + 1) → ℤ, y ≠ 0 →
      (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α < ‖toE (m + 1) y‖ →
      ‖toE (m + 1) y‖ + Real.sqrt ((m + 1 : ℕ) : ℝ) / 2 ≤ windowR2 α (m + 1) →
        y ∈ RawDataInst2RW2.shellR α (m + 1))
    (hfree : ∀ y : Fin (m + 1) → ℤ, y ≠ 0 →
      ‖toE (m + 1) y‖ ≤ (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α → y ∉ latZ p (m + 1) g)
    (hband : BandHypR2 p m α mLow g) :
    ∀ y : Fin (m + 1) → ℤ, y ≠ 0 → y ∈ latZ p (m + 1) g →
      (WithLp.toLp 2 (xOf α y) : EuclideanSpace ℝ (Fin (m + 1)))
        ∉ ChainEllipsoid.ellipsoid (symMat A) := by
  intro y hy0 hylat
  by_cases hshort : ‖toE (m + 1) y‖ ≤ (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α
  · exact absurd hylat (hfree y hy0 hshort)
  have hlong : (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α < ‖toE (m + 1) y‖ := not_le.1 hshort
  by_cases hin : ‖toE (m + 1) y‖ + Real.sqrt ((m + 1 : ℕ) : ℝ) / 2 ≤ windowR2 α (m + 1)
  · exact DriftStopped8.notMem_ellipsoid_of_mem_kSet hkSet
      (mem_windowOfR2.2 ⟨hcov y hy0 hlong hin, hylat⟩)
  · have hfar : windowR2 α (m + 1) - Real.sqrt ((m + 1 : ℕ) : ℝ) / 2 < ‖toE (m + 1) y‖ := by
      have hgt := not_le.1 hin
      linarith
    have hreach := hband y hy0 hylat hfar
    rw [← DriftStopped8.norm_toLp_xOf hα.le y] at hreach
    exact DriftStopped8.notMem_ellipsoid_of_reach hSB hreach

/-! ## 4. The state supply and the drift side at `mAt` -/

/-- **The state supply at the generic reach window and the repaired threshold.** -/
def StateSupplyAdoptedR2 (c₃ : ℕ → ℝ) (w : ∀ _p m : ℕ, ℝ → (Fin (m + 1) → ℤ) → ℝ≥0∞)
    (θ : ℕ → ℕ → ℝ → ℝ≥0∞) (C' : ℝ) : Prop :=
  ∀ m : ℕ, Threshold2.n₁ ≤ m → ∀ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p) (α : ℝ),
    0 < α → ∀ (_hn : 3 ≤ m + 1)
      (_hraw : PaddedLawSetupRW2.RawDataR p (m + 1) α ((1 - 1 / ((m + 1 : ℕ) : ℝ)) / α)
        (qC α) (RawDataInst2RW2.shellR α (m + 1)) (A0C (m + 1)))
      (_hnd : TailSideSetup2.NormData (m + 1) α (qC α)
        (RawDataInst2RW2.shellR α (m + 1)) (A0C (m + 1))),
      (∀ y : Fin (m + 1) → ℤ, y ≠ 0 →
        (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α < ‖toE (m + 1) y‖ →
        ‖toE (m + 1) y‖ + Real.sqrt ((m + 1 : ℕ) : ℝ) / 2 ≤ windowR2 α (m + 1) →
          y ∈ RawDataInst2RW2.shellR α (m + 1)) →
      ∀ (g : Fin (m + 1) → ZMod p), g ≠ 0 →
      (∀ y : Fin (m + 1) → ℤ, y ≠ 0 →
        ‖toE (m + 1) y‖ ≤ (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α → y ∉ latZ p (m + 1) g) →
      Theorem2.LightContact (w p m α) (RawDataInst2RW2.shellR α (m + 1)) (θ p m α) g →
      ∃ (A : EuclideanSpace ℝ (UT (m + 1))) (M : ℝ),
        A ∈ Chain.kSet (qC α) (windowOfR2 α p m g) ∧
        Discharge.StateBounds (symMat A) (mAt (m + 1) (c₃ (m + 1))) M ∧
        ChainWiring.logDet A ≤ C' - 4 * Real.log ((m + 1 : ℕ) : ℝ)

/-- **The drift side at the generic reach window.** -/
def DriftSideW2 (w : ∀ _p m : ℕ, ℝ → (Fin (m + 1) → ℤ) → ℝ≥0∞) (θ : ℕ → ℕ → ℝ → ℝ≥0∞)
    (c₀ : ℝ) : Prop :=
  ∀ m : ℕ, Threshold2.n₁ ≤ m → ∀ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p) (α : ℝ),
    0 < α → ∀ (_hn : 3 ≤ m + 1)
      (_hraw : PaddedLawSetupRW2.RawDataR p (m + 1) α ((1 - 1 / ((m + 1 : ℕ) : ℝ)) / α)
        (qC α) (RawDataInst2RW2.shellR α (m + 1)) (A0C (m + 1)))
      (_hnd : TailSideSetup2.NormData (m + 1) α (qC α)
        (RawDataInst2RW2.shellR α (m + 1)) (A0C (m + 1))),
      (∀ y : Fin (m + 1) → ℤ, y ≠ 0 →
        (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α < ‖toE (m + 1) y‖ →
        ‖toE (m + 1) y‖ + Real.sqrt ((m + 1 : ℕ) : ℝ) / 2 ≤ windowR2 α (m + 1) →
          y ∈ RawDataInst2RW2.shellR α (m + 1)) →
      ∀ (g : Fin (m + 1) → ZMod p), g ≠ 0 →
      (∀ y : Fin (m + 1) → ℤ, y ≠ 0 →
        ‖toE (m + 1) y‖ ≤ (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α → y ∉ latZ p (m + 1) g) →
      Theorem2.LightContact (w p m α) (RawDataInst2RW2.shellR α (m + 1)) (θ p m α) g →
      Assembly.ChainOutput α g c₀

/-- **Goal (5) at the generic reach window**, with the band discharged by `bandSideAdoptedR2` for
every admissible `c₃`.  `c₀ = exp(−C'/2)` is produced. -/
theorem driftSideW2_of_stateSupplyR2 {c₃ : ℕ → ℝ} (hc₃0 : ∀ n, 0 ≤ c₃ n)
    (hc₃ : ∀ n, c₃ n * DriftStopped6.etaAdopted n ≤ 1 / 4)
    {w : ∀ _p m : ℕ, ℝ → (Fin (m + 1) → ℤ) → ℝ≥0∞} {θ : ℕ → ℕ → ℝ → ℝ≥0∞} {C' : ℝ}
    (h : StateSupplyAdoptedR2 c₃ w θ C') :
    ∃ c₀ : ℝ, 0 < c₀ ∧ DriftSideW2 w θ c₀ := by
  refine ⟨Real.exp (-C' / 2), Real.exp_pos _, ?_⟩
  intro m hm p hp hp0 α hα hn hraw hnd hcov g hg hfree hlight
  obtain ⟨A, M, hkSet, hSB, hlog⟩ := h m hm p hp hp0 α hα hn hraw hnd hcov g hg hfree hlight
  have hm0 : m ≠ 0 := by
    have h2 : 2073600 ≤ m := by simpa [Threshold2.n₁] using hm
    omega
  exact DriftStopped8.chainOutput_of_state hm0 hSB hlog
    (avoid_of_casesR2 hα hSB hkSet hcov hfree (bandSideAdoptedR2 hc₃0 hc₃ m hm p α hα g))

end Submission.L10.DriftStopped8R5

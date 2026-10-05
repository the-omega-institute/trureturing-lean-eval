import Submission.L10.PaddedLawSetup
import Submission.L10.WindowR2
import Submission.L10.ChainWalkRW2

/-!
# Gate L-10 — `RawData` at the reach window (`windowR2`)

Brief 73, part 1.  Report 68 §2: `PaddedLawSetup.RawData` names `windowC` in exactly three of its
fifteen fields — `window_lt_p`, `supp_radius`, `hwin` — and nothing else in `PaddedLawSetup` names
the window at all.  `RawDataR` is that structure with those three fields moved out to
`WindowR2.windowR2`.

**`TailSideHyp` is window-free**, so the R lane reuses it verbatim: `TailSideHypR` is a
`@[reducible]` alias, not a copy.  Report 68 §2 lists `PaddedLawSetup.TailSideHyp ×3`; the three
occurrences it counted are `RawData`'s, not `TailSideHyp`'s (checked by grep, `PaddedLawSetup.lean`
lines 277, 279, 280 — all inside `RawData`).

`chainRaw2_on_setupR`, `TailSideR` and `tailSide_on_setupR` compose brief 72's
`Submission.L10.chainRaw2_of_walkRW2` and `ChainRaw2RW2` exactly as the originals compose
`chainRaw2_of_walk` and `ChainRaw2`.

**Neither structure implies the other.**  `windowC α n ≤ windowR2 α n`
(`WindowR2.windowC_le_windowR2`), so `supp_radius` and `hwin` are *weaker* at `windowR2` while
`window_lt_p` is *stronger*.  `rawDataR_of_rawData` is therefore not provable, and is not stated.
-/

set_option linter.unusedSectionVars false

namespace Submission.L10.PaddedLawSetupRW2

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal RealInnerProductSpace
open Submission.L10 Submission.L10.Increments Submission.L10.ChainSetup
open Submission.L10.Tiling Submission.L10.Section5 Submission.L10.ConstructionA
open Submission.L10.PaddedLawSetup Submission.L10.WindowR2

noncomputable section

/-- **The tail-side hypothesis is unchanged.**  `PaddedLawSetup.TailSideHyp` does not mention the
window, so the reach lane uses it as it stands. -/
@[reducible] def TailSideHypR (n : ℕ) (c α : ℝ)
    (q : (Fin n → ℤ) → EuclideanSpace ℝ (UT n)) (W : Finset (Fin n → ℤ))
    (A₀ : EuclideanSpace ℝ (UT n)) : Prop :=
  TailSideHyp n c α q W A₀

/-- **`PaddedLawSetup.RawData` at the reach window.**  Identical field for field except
`window_lt_p`, `supp_radius` and `hwin`, which are stated at `WindowR2.windowR2 α n`. -/
structure RawDataR (p n : ℕ) (α R : ℝ) (q : (Fin n → ℤ) → EuclideanSpace ℝ (UT n))
    (W : Finset (Fin n → ℤ)) (A₀ : EuclideanSpace ℝ (UT n)) : Prop where
  hq : ∀ j : (Fin n → ℤ), ∀ i ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫
  hA₀ : ∀ y ∈ W, (1 : ℝ) < ⟪A₀, q y⟫
  alpha_pos : 0 < α
  alpha_norm : α ^ n * ((p ^ (n - 1) : ℕ) : ℝ) = kappa n
  R_nonneg : 0 ≤ R
  R_scaled : α * R ≤ 1 - 1 / (n : ℝ)
  R_lt_p : R < (p : ℝ)
  tiling_defect : (n : ℝ) * (α * Real.sqrt n / 2) ≤ 1 / 4
  window_lt_p : windowR2 α n < (p : ℝ)
  supp_ne_zero : ∀ y ∈ W, y ≠ 0
  supp_radius : ∀ y ∈ W, ‖toE n y‖ ≤ windowR2 α n
  hwin : ∀ y ∈ W, ‖toE n y‖ + Real.sqrt n / 2 ≤ windowR2 α n
  hr : ∀ y ∈ W, 0 < α * ‖toE n y‖
  hy : ∀ k, k < ParamsAdopted2.numStepsAdopted2 n → k ≠ 0 → ∀ y ∈ W,
    0 < yOf (a0C n) ((k : ℝ) * ParamsAdopted2.stepSizeAdopted2 n) (α * ‖toE n y‖)
  arith : (n : ℝ) * kappa n * ((p : ℝ) - 1) * (8 - 8 / (n : ℝ) ^ 2) < 8 * ((p : ℝ) ^ n - 1)

/-- **`RawDataR` restricts**, exactly as `LatticeData.rawData_mono` does for `RawData`: every field
is either `∀ y ∈ W` or independent of `W`. -/
theorem rawDataR_mono {p n : ℕ} {α R : ℝ} {q : (Fin n → ℤ) → EuclideanSpace ℝ (UT n)}
    {W W' : Finset (Fin n → ℤ)} {A₀ : EuclideanSpace ℝ (UT n)}
    (h : RawDataR p n α R q W A₀) (hsub : W' ⊆ W) : RawDataR p n α R q W' A₀ :=
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

/-! ### The chain on `chainSetup`, at the reach window -/

/-- **`ChainRaw2RW2` on `chainSetup`.**  `PaddedLawSetup.chainRaw2_on_setup` with brief 72's
`chainRaw2_of_walkRW2`; the fifteen `RawDataR` fields and the one probabilistic hypothesis are
passed in the same order. -/
noncomputable def chainRaw2_on_setupR {n p : ℕ} {c α : ℝ}
    {q : (Fin n → ℤ) → EuclideanSpace ℝ (UT n)} {W : Finset (Fin n → ℤ)}
    {A₀ : EuclideanSpace ℝ (UT n)} {R : ℝ} (hn : 3 ≤ n)
    (hdata : RawDataR p n α R q W A₀) (htail : TailSideHypR n c α q W A₀) :
    ChainRaw2RW2 p n :=
  chainRaw2_of_walkRW2 (P := gaussPath (EuclideanSpace ℝ (UT n))) (ξ := step c)
    hn hdata.hq hdata.hA₀ hdata.alpha_pos hdata.alpha_norm R hdata.R_nonneg
    hdata.R_scaled hdata.R_lt_p hdata.tiling_defect hdata.window_lt_p hdata.supp_ne_zero
    hdata.supp_radius hdata.hwin hdata.hr hdata.hy htail hdata.arith

/-- **The tail-side component of `ChainDelivers` at the reach window.** -/
def TailSideR : Prop :=
  ∀ m : ℕ, Threshold2.n₁ ≤ m →
    ∃ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p), Nonempty (ChainRaw2RW2 p (m + 1))

/-- **The tail side on `chainSetup`, at the reach window.** -/
theorem tailSide_on_setupR
    (h : ∀ m : ℕ, Threshold2.n₁ ≤ m →
      ∃ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p) (c α R : ℝ)
        (q : (Fin (m + 1) → ℤ) → EuclideanSpace ℝ (UT (m + 1)))
        (W : Finset (Fin (m + 1) → ℤ)) (A₀ : EuclideanSpace ℝ (UT (m + 1))),
        3 ≤ m + 1 ∧ RawDataR p (m + 1) α R q W A₀ ∧ TailSideHypR (m + 1) c α q W A₀) :
    TailSideR := by
  intro m hm
  obtain ⟨p, hp, hp0, c, α, R, q, W, A₀, hn, hdata, htail⟩ := h m hm
  exact ⟨p, hp, hp0, ⟨chainRaw2_on_setupR hn hdata htail⟩⟩

/-- The two fields `TailSideSetup2.tailSideHyp_of_rawData` actually reads — checked by grep over
its proof (`TailSideSetup2.lean:158–225`): `hraw.hA₀` twice and `hraw.hr` once, and no other field.
Recording them here is what makes the gap in the report precise. -/
theorem hA₀_and_hr {p n : ℕ} {α R : ℝ} {q : (Fin n → ℤ) → EuclideanSpace ℝ (UT n)}
    {W : Finset (Fin n → ℤ)} {A₀ : EuclideanSpace ℝ (UT n)} (h : RawDataR p n α R q W A₀) :
    (∀ y ∈ W, (1 : ℝ) < ⟪A₀, q y⟫) ∧ (∀ y ∈ W, 0 < α * ‖toE n y‖) :=
  ⟨h.hA₀, h.hr⟩

end

end Submission.L10.PaddedLawSetupRW2

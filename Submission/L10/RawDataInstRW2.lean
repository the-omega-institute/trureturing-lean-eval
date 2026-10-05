import Mathlib
import Submission.L10.RawDataInst
import Submission.L10.PaddedLawSetupRW2

/-!
# Gate L-10 — `RawDataR` for every dimension: the numeric half at the reach window

Brief 73, part 2.  `RawDataInst.rawData_of_lattice` with `windowC` replaced by
`WindowR2.windowR2`.  Report 68 §4 priced this at ~25 lines and said the new `window_lt_p` is "free
through `exists_prime_alpha_mul`"; that is confirmed — the only changes are

* the threshold handed to `exists_prime_alpha_mul` is `max (2·reachNum2 n) (max 1 √n)` rather than
  `max (2·winNum n) (max 1 √n)`, which `exists_prime_alpha_mul` clears for *any* `M`, and
* `window_lt_p` is discharged by `WindowR2.windowR2_lt_p` instead of by `windowC_eq` and `linarith`.

**One hypothesis genuinely strengthens.**  `WindowR2.windowR2_lt_p` needs `2073600 ≤ n`, where the
`windowC` proof needed only `2 ≤ n`, because `1 < reachNum2 n` is proved from
`DriftStopped6.mAdopted n < 1` at the threshold.  Every consumer runs at `n = m + 1` with
`m ≥ Threshold2.n₁ = 2073600`, so this costs nothing.
-/

set_option linter.unusedSectionVars false

open MeasureTheory Finset
open scoped RealInnerProductSpace

namespace Submission.L10.RawDataInstRW2

open Submission.L10 Submission.L10.Section5 Submission.L10.Tiling
open Submission.L10.Increments Submission.L10.ConstructionA
open Submission.L10.PaddedLawSetup Submission.L10.PaddedLawSetupRW2
open Submission.L10.RawDataInst Submission.L10.WindowR2

variable {n : ℕ}

/-- **`RawDataR`, eight numeric fields proved.**  The seven `q`/`W`/`A₀` fields are hypotheses, as
in `RawDataInst.rawData_of_lattice`; `R` is Klartag's `(1−1/n)/α`. -/
theorem rawData_of_latticeR (hn : 2073600 ≤ n) {p : ℕ} {α : ℝ} (hαpos : 0 < α) (hp2 : 2 ≤ p)
    (hαnorm : α ^ n * ((p ^ (n - 1) : ℕ) : ℝ) = kappa n)
    (hαsmall : α ≤ 1 / (2 * (n : ℝ) * Real.sqrt n))
    (hM : max (2 * reachNum2 n) (max 1 (Real.sqrt n)) ≤ α * (p : ℝ))
    {q : (Fin n → ℤ) → EuclideanSpace ℝ (Increments.UT n)} {W : Finset (Fin n → ℤ)}
    {A₀ : EuclideanSpace ℝ (Increments.UT n)}
    (hq : ∀ j : (Fin n → ℤ), ∀ i ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫)
    (hA₀ : ∀ y ∈ W, (1 : ℝ) < ⟪A₀, q y⟫)
    (hne0 : ∀ y ∈ W, y ≠ 0) (hrad : ∀ y ∈ W, ‖toE n y‖ ≤ windowR2 α n)
    (hwin : ∀ y ∈ W, ‖toE n y‖ + Real.sqrt n / 2 ≤ windowR2 α n)
    (hr : ∀ y ∈ W, 0 < α * ‖toE n y‖)
    (hy : ∀ k, k < ParamsAdopted2.numStepsAdopted2 n → k ≠ 0 → ∀ y ∈ W,
      0 < yOf (a0C n) ((k : ℝ) * ParamsAdopted2.stepSizeAdopted2 n) (α * ‖toE n y‖)) :
    RawDataR p n α ((1 - 1 / (n : ℝ)) / α) q W A₀ := by
  have hn2 : 2 ≤ n := by omega
  have hn0 : 0 < n := by omega
  have hnr : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hn2r : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hsq1 : (1 : ℝ) ≤ Real.sqrt n := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hnr
  have hppos : (0 : ℝ) < (p : ℝ) := by
    have : 0 < p := by omega
    exact_mod_cast this
  have hDpos : (0 : ℝ) < 2 * (n : ℝ) * Real.sqrt n := by positivity
  have hmul : α * (2 * (n : ℝ) * Real.sqrt n) ≤ 1 := (le_div_iff₀ hDpos).1 hαsmall
  have hone : (1 : ℝ) ≤ α * (p : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hM
  have h2w : 2 * reachNum2 n ≤ α * (p : ℝ) := le_trans (le_max_left _ _) hM
  have hfrac : (0 : ℝ) ≤ 1 - 1 / (n : ℝ) := by
    have : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  have hsnn : (0 : ℝ) ≤ α * Real.sqrt n := by positivity
  have hsn : α * Real.sqrt n ≤ 1 := by nlinarith [hmul, hsnn, hn2r, hsq1]
  refine ⟨hq, hA₀, hαpos, hαnorm, by positivity, ?_, ?_, ?_, ?_, hne0, hrad, hwin, hr, hy, ?_⟩
  · rw [mul_div_cancel₀ _ hαpos.ne']
  · rw [div_lt_iff₀ hαpos]
    calc 1 - 1 / (n : ℝ) < 1 := by
          have hinv : (0 : ℝ) < 1 / (n : ℝ) := by positivity
          linarith
      _ ≤ α * (p : ℝ) := hone
      _ = (p : ℝ) * α := mul_comm _ _
  · have hrw : (n : ℝ) * (α * Real.sqrt n / 2) = α * (2 * (n : ℝ) * Real.sqrt n) / 4 := by ring
    rw [hrw]; linarith [hmul]
  · exact windowR2_lt_p hn hαpos h2w hsn
  · -- `arith`, unchanged: it does not mention the window
    have hκ : 0 < kappa n := kappa_pos hn0
    have hpn : (p : ℝ) ^ n = ((p ^ n : ℕ) : ℝ) := by push_cast; ring
    have hκp : kappa n * (p : ℝ) = (α * (p : ℝ)) ^ n := by
      rw [mul_pow, show n = (n - 1) + 1 by omega, pow_succ (p : ℝ) (n - 1),
        show (n - 1) + 1 = n by omega, ← hαnorm]
      push_cast; ring
    have hαn : (n : ℝ) * α ^ n ≤ 1 / 2 := by
      have h1 : α ≤ 1 / (2 * (n : ℝ)) := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith [hmul, hsq1]
      have h2 : α ^ n ≤ (1 / (2 * (n : ℝ))) ^ n := pow_le_pow_left₀ hαpos.le h1 n
      have h3 : (1 / (2 * (n : ℝ))) ^ n ≤ (1 / (2 * (n : ℝ))) ^ 2 := by
        apply pow_le_pow_of_le_one (by positivity) _ hn2
        rw [div_le_one (by positivity)]; linarith
      have h4 : (1 / (2 * (n : ℝ))) ^ 2 = 1 / (4 * (n : ℝ) ^ 2) := by field_simp; ring
      have h5 : α ^ n ≤ 1 / (4 * (n : ℝ) ^ 2) := by rw [← h4]; linarith [h2, h3]
      have h6 : (n : ℝ) * α ^ n ≤ (n : ℝ) * (1 / (4 * (n : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left h5 (by linarith)
      have h7 : (n : ℝ) * (1 / (4 * (n : ℝ) ^ 2)) = 1 / (4 * (n : ℝ)) := by field_simp
      have h8 : 1 / (4 * (n : ℝ)) ≤ 1 / 2 :=
        one_div_le_one_div_of_le (by norm_num) (by linarith)
      linarith [h6, h7, h8]
    have hp2r : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    have hpn2 : (2 : ℝ) ≤ (p : ℝ) ^ n := by
      have ha : (2 : ℝ) ^ n ≤ (p : ℝ) ^ n := pow_le_pow_left₀ (by norm_num) hp2r n
      have hb : (2 : ℝ) ≤ (2 : ℝ) ^ n := by
        calc (2 : ℝ) = 2 ^ 1 := by norm_num
          _ ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    have hkey : (n : ℝ) * (kappa n * (p : ℝ)) + 1 ≤ (p : ℝ) ^ n := by
      have hid : (n : ℝ) * (kappa n * (p : ℝ)) = ((n : ℝ) * α ^ n) * (p : ℝ) ^ n := by
        rw [hκp, mul_pow]; ring
      rw [hid]
      nlinarith [hαn, hpn2]
    have hfin : (n : ℝ) * kappa n * ((p : ℝ) - 1) * (8 - 8 / (n : ℝ) ^ 2)
        < 8 * ((p : ℝ) ^ n - 1) := by
      have h8 : 8 - 8 / (n : ℝ) ^ 2 < 8 := by
        have hq8 : (0 : ℝ) < 8 / (n : ℝ) ^ 2 := by positivity
        linarith
      have hpos1 : 0 < (n : ℝ) * kappa n * ((p : ℝ) - 1) := by
        have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
        positivity
      nlinarith [hkey, h8, hpos1, hκ, hppos]
    rw [hpn] at hfin ⊢
    exact hfin

/-- **`exists_rawDataR`, modulo the lattice data.**  `p` and `α` come from
`RawDataInst.exists_prime_alpha_mul` at `M = max (2·reachNum2 n) (max 1 √n)`. -/
theorem exists_rawDataR (hn : 2073600 ≤ n)
    (hlat : ∀ (p : ℕ) (α : ℝ), 0 < α → 2 ≤ p →
      ∃ (q : (Fin n → ℤ) → EuclideanSpace ℝ (Increments.UT n)) (W : Finset (Fin n → ℤ))
        (A₀ : EuclideanSpace ℝ (Increments.UT n)),
        (∀ j : (Fin n → ℤ), ∀ i ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) ∧
        (∀ y ∈ W, (1 : ℝ) < ⟪A₀, q y⟫) ∧ (∀ y ∈ W, y ≠ 0) ∧
        (∀ y ∈ W, ‖toE n y‖ ≤ windowR2 α n) ∧
        (∀ y ∈ W, ‖toE n y‖ + Real.sqrt n / 2 ≤ windowR2 α n) ∧
        (∀ y ∈ W, 0 < α * ‖toE n y‖) ∧
        (∀ k, k < ParamsAdopted2.numStepsAdopted2 n → k ≠ 0 → ∀ y ∈ W,
          0 < yOf (a0C n) ((k : ℝ) * ParamsAdopted2.stepSizeAdopted2 n) (α * ‖toE n y‖))) :
    ∃ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p) (α R : ℝ)
      (q : (Fin n → ℤ) → EuclideanSpace ℝ (Increments.UT n)) (W : Finset (Fin n → ℤ))
      (A₀ : EuclideanSpace ℝ (Increments.UT n)), RawDataR p n α R q W A₀ := by
  obtain ⟨p, hp, α, hαpos, hαnorm, hαsmall, hM⟩ :=
    exists_prime_alpha_mul (by omega : 2 ≤ n) (max (2 * reachNum2 n) (max 1 (Real.sqrt n)))
      (le_trans (le_max_left _ _) (le_max_right _ _))
  have hp2 : 2 ≤ p := hp.two_le
  obtain ⟨q, W, A₀, hq, hA₀, hne0, hrad, hwin, hr, hy⟩ := hlat p α hαpos hp2
  exact ⟨p, ⟨hp⟩, ⟨hp.ne_zero⟩, α, (1 - 1 / (n : ℝ)) / α, q, W, A₀,
    rawData_of_latticeR hn hαpos hp2 hαnorm hαsmall hM hq hA₀ hne0 hrad hwin hr hy⟩

end Submission.L10.RawDataInstRW2

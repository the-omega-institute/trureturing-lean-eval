import Mathlib
import Submission.L10.PaddedLawSetup
import Submission.L10.Section5
import Submission.L10.Lemma43Uniform

/-!
# Gate L-10 — `RawData` for every dimension: the non-probabilistic half of HOLE 52

Brief 61.  `PaddedLawSetup.RawData` has **fifteen** fields (`:269–284`), not the eleven the brief
counted: `hwin`, `hr`, `hy` and `arith` follow `supp_radius`.  Eight are about `p`, `α` and `R`
alone and are **proved** here; the other seven mention `q`, `W`, `A₀` and are hypotheses, because
those three objects exist nowhere in the tree — every module carries them abstractly (report 61 §3).

## The one idea

Everything `RawData` asks of `p` and `α` reduces to a lower bound on the **product** `α·p`,
because `(α·p)^n = κ_n·p` follows from `alpha_norm`.  `exists_prime_alpha_mul` gets `α·p` above
any prescribed `M` by feeding `Section5.exists_prime_alpha_le` the threshold
`ε = min (κ_n / M^{n-1}) (1/(2n√n))`: the first factor forces `p ≥ M^n/κ_n`, hence `κ_n p ≥ M^n`,
hence `α p ≥ M`; the second is the tiling defect.  Then

* `R_lt_p` needs `1 ≤ α·p`;
* `window_lt_p` needs `2·winNum n ≤ α·p` and `√n ≤ α·p`, since
  `windowC α n = winNum n / α + √n/2` **by `rfl`**;
* `arith` needs only `α ≤ 1/(2n)` and `p ≥ 2`.

`R` is Klartag's `(1 − 1/n)/α`, which makes `R_scaled` an equality.  It is the radius at which
`Section5.exists_good_line_of_chainData` proves the drift side's R-condition
(`∀ y ≠ 0, ‖toE n y‖ ≤ d.R → y ∉ latZ p n g`), and `TailAtStep.params_of_raw2` sets
`Params.R := Q.R`, so the choice made here is the one that reaches the drift side unchanged.
-/

set_option linter.unusedSectionVars false

open MeasureTheory Finset
open scoped RealInnerProductSpace

namespace Submission.L10.RawDataInst

open Submission.L10 Submission.L10.Section5 Submission.L10.Tiling
open Submission.L10.ConstructionA Submission.L10.PaddedLawSetup

variable {n : ℕ}

/-! ### 1. The prime choice: `α·p` as large as we please -/

/-- **The prime choice.**  `Section5.exists_prime_alpha_le` with the threshold chosen so that the
*product* `α·p` clears any prescribed `M`.  Everything `RawData` asks of `p` and `α` beyond the
lattice data reduces to a lower bound on `α·p`, because `(α·p)^n = κ_n·p`. -/
theorem exists_prime_alpha_mul (hn : 2 ≤ n) (M : ℝ) (hM : 1 ≤ M) :
    ∃ p : ℕ, Nat.Prime p ∧ ∃ α : ℝ, 0 < α ∧
      α ^ n * ((p ^ (n - 1) : ℕ) : ℝ) = kappa n ∧
      α ≤ 1 / (2 * (n : ℝ) * Real.sqrt n) ∧
      M ≤ α * (p : ℝ) := by
  have hn0 : 0 < n := by omega
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
  have hsq : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.2 hnr
  have hκ : 0 < kappa n := kappa_pos hn0
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM
  set ε : ℝ := min (kappa n / M ^ (n - 1)) (1 / (2 * (n : ℝ) * Real.sqrt n)) with hε
  have hεpos : 0 < ε := lt_min (by positivity) (by positivity)
  obtain ⟨p, hp, α, hαpos, hαnorm, hαle⟩ := Section5.exists_prime_alpha_le hn hεpos
  refine ⟨p, hp, α, hαpos, hαnorm, le_trans hαle (min_le_right _ _), ?_⟩
  -- `p ^ (n-1) = κ_n / α ^ n ≥ (M ^ n / κ_n) ^ (n-1)`
  have hα1 : α ≤ kappa n / M ^ (n - 1) := le_trans hαle (min_le_left _ _)
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hαn : (0 : ℝ) < α ^ n := by positivity
  have hnorm' : α ^ n * (p : ℝ) ^ (n - 1) = kappa n := by
    rw [← hαnorm]; push_cast; ring
  have hpn : (p : ℝ) ^ (n - 1) = kappa n / α ^ n := by
    field_simp
    linarith [hnorm']
  have hMn : (0 : ℝ) < M ^ (n - 1) := by positivity
  have hstep : α ^ n ≤ (kappa n / M ^ (n - 1)) ^ n := pow_le_pow_left₀ hαpos.le hα1 n
  have hdiv : kappa n / (kappa n / M ^ (n - 1)) ^ n ≤ kappa n / α ^ n :=
    div_le_div_of_nonneg_left hκ.le hαn hstep
  have heq : kappa n / (kappa n / M ^ (n - 1)) ^ n = (M ^ n / kappa n) ^ (n - 1) := by
    rw [div_pow, div_pow, ← pow_mul, ← pow_mul]
    rw [mul_comm (n - 1) n,
      show (kappa n) ^ n = kappa n ^ (n - 1) * kappa n by
        rw [← pow_succ]; congr 1; omega]
    field_simp
  have hb : (M ^ n / kappa n) ^ (n - 1) ≤ (p : ℝ) ^ (n - 1) := by
    rw [← heq, hpn]; exact hdiv
  have hn1 : n - 1 ≠ 0 := by omega
  have hn0' : n ≠ 0 := by omega
  have hp' : M ^ n / kappa n ≤ (p : ℝ) := le_of_pow_le_pow_left₀ hn1 hppos.le hb
  have hMnle : M ^ n ≤ kappa n * (p : ℝ) := by
    rw [div_le_iff₀ hκ] at hp'; linarith [hp']
  have hprod : (α * (p : ℝ)) ^ n = kappa n * (p : ℝ) := by
    rw [mul_pow, show n = (n - 1) + 1 by omega, pow_succ (p : ℝ) (n - 1)]
    rw [show (n - 1) + 1 = n by omega]
    calc α ^ n * ((p : ℝ) ^ (n - 1) * (p : ℝ))
        = (α ^ n * (p : ℝ) ^ (n - 1)) * (p : ℝ) := by ring
      _ = kappa n * (p : ℝ) := by rw [hnorm']
  exact le_of_pow_le_pow_left₀ hn0' (by positivity) (by rw [hprod]; exact hMnle)

/-! ### 2. `RawData` from the lattice data -/

/-- The window's numerator: `windowC α n = winNum n / α + √n/2`, by `rfl`. -/
noncomputable def winNum (n : ℕ) : ℝ :=
  subst (a0C n) (Real.sqrt (ChainDrift.horizon n)) (Real.log n)

theorem windowC_eq (α : ℝ) (n : ℕ) : windowC α n = winNum n / α + Real.sqrt n / 2 := rfl

/-- **`RawData`, eight numeric fields proved.**  `hq`, `hA₀`, `supp_ne_zero`, `supp_radius`,
`hwin`, `hr`, `hy` mention `q`, `W`, `A₀` and are the hypotheses; everything about `p`, `α` and
`R` is discharged from `exists_prime_alpha_mul`'s output. `R` is Klartag's `(1-1/n)/α`, the
radius at which `Section5.exists_good_line_of_chainData` proves the R-condition. -/
theorem rawData_of_lattice (hn : 2 ≤ n) {p : ℕ} {α : ℝ} (hαpos : 0 < α) (hp2 : 2 ≤ p)
    (hαnorm : α ^ n * ((p ^ (n - 1) : ℕ) : ℝ) = kappa n)
    (hαsmall : α ≤ 1 / (2 * (n : ℝ) * Real.sqrt n))
    (hM : max (2 * winNum n) (max 1 (Real.sqrt n)) ≤ α * (p : ℝ))
    {q : (Fin n → ℤ) → EuclideanSpace ℝ (Increments.UT n)} {W : Finset (Fin n → ℤ)}
    {A₀ : EuclideanSpace ℝ (Increments.UT n)}
    (hq : ∀ j : (Fin n → ℤ), ∀ i ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫)
    (hA₀ : ∀ y ∈ W, (1 : ℝ) < ⟪A₀, q y⟫)
    (hne0 : ∀ y ∈ W, y ≠ 0) (hrad : ∀ y ∈ W, ‖toE n y‖ ≤ windowC α n)
    (hwin : ∀ y ∈ W, ‖toE n y‖ + Real.sqrt n / 2 ≤ windowC α n)
    (hr : ∀ y ∈ W, 0 < α * ‖toE n y‖)
    (hy : ∀ k, k < ParamsAdopted2.numStepsAdopted2 n → k ≠ 0 → ∀ y ∈ W,
      0 < yOf (a0C n) ((k : ℝ) * ParamsAdopted2.stepSizeAdopted2 n) (α * ‖toE n y‖)) :
    RawData p n α ((1 - 1 / (n : ℝ)) / α) q W A₀ := by
  have hn0 : 0 < n := by omega
  have hnr : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hn2r : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsq1 : (1 : ℝ) ≤ Real.sqrt n := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hnr
  have hppos : (0 : ℝ) < (p : ℝ) := by
    have : 0 < p := by omega
    exact_mod_cast this
  have hDpos : (0 : ℝ) < 2 * (n : ℝ) * Real.sqrt n := by positivity
  have hmul : α * (2 * (n : ℝ) * Real.sqrt n) ≤ 1 := (le_div_iff₀ hDpos).1 hαsmall
  have hone : (1 : ℝ) ≤ α * (p : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hM
  have hsqp : Real.sqrt n ≤ α * (p : ℝ) :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hM
  have h2w : 2 * winNum n ≤ α * (p : ℝ) := le_trans (le_max_left _ _) hM
  have hfrac : (0 : ℝ) ≤ 1 - 1 / (n : ℝ) := by
    have : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  have hαlt1 : α < 1 := by nlinarith [hmul, hsq1, hn2r]
  have hsqlt : Real.sqrt n < (p : ℝ) := by nlinarith [hsqp, hαlt1, hppos]
  refine ⟨hq, hA₀, hαpos, hαnorm, by positivity, ?_, ?_, ?_, ?_, hne0, hrad, hwin, hr, hy, ?_⟩
  · rw [mul_div_cancel₀ _ hαpos.ne']
  · rw [div_lt_iff₀ hαpos]
    have hinv : (0 : ℝ) < 1 / (n : ℝ) := by positivity
    calc 1 - 1 / (n : ℝ) < 1 := by linarith
      _ ≤ α * (p : ℝ) := hone
      _ = (p : ℝ) * α := mul_comm _ _
  · have hrw : (n : ℝ) * (α * Real.sqrt n / 2) = α * (2 * (n : ℝ) * Real.sqrt n) / 4 := by ring
    rw [hrw]; linarith [hmul]
  · rw [windowC_eq]
    have h1 : winNum n / α ≤ (p : ℝ) / 2 := by
      rw [div_le_iff₀ hαpos]
      nlinarith [h2w]
    linarith [h1, hsqlt]
  · -- `arith`
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
        apply pow_le_pow_of_le_one (by positivity) _ hn
        rw [div_le_one (by positivity)]; linarith
      have h4 : (1 / (2 * (n : ℝ))) ^ 2 = 1 / (4 * (n : ℝ) ^ 2) := by field_simp; ring
      have h5 : α ^ n ≤ 1 / (4 * (n : ℝ) ^ 2) := by rw [← h4]; linarith [h2, h3]
      have h6 : (n : ℝ) * α ^ n ≤ (n : ℝ) * (1 / (4 * (n : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left h5 (by linarith)
      have h7 : (n : ℝ) * (1 / (4 * (n : ℝ) ^ 2)) = 1 / (4 * (n : ℝ)) := by
        field_simp
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
      have : (n : ℝ) * (kappa n * (p : ℝ)) = ((n : ℝ) * α ^ n) * (p : ℝ) ^ n := by
        rw [hκp, mul_pow]; ring
      rw [this]
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

/-! ### 3. `rawData_exists`, and HOLE 52 -/

/-- **`rawData_exists`, modulo the lattice data.**  `p` and `α` come from
`exists_prime_alpha_mul` at `M = max (2·winNum n) (max 1 √n)`; `R = (1-1/n)/α`.  `hlat` is the
seven `q`/`W`/`A₀` fields, which no module in the tree supplies (report 61 §3). -/
theorem exists_rawData (hn : 2 ≤ n)
    (hlat : ∀ (p : ℕ) (α : ℝ), 0 < α → 2 ≤ p →
      ∃ (q : (Fin n → ℤ) → EuclideanSpace ℝ (Increments.UT n)) (W : Finset (Fin n → ℤ))
        (A₀ : EuclideanSpace ℝ (Increments.UT n)),
        (∀ j : (Fin n → ℤ), ∀ i ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) ∧
        (∀ y ∈ W, (1 : ℝ) < ⟪A₀, q y⟫) ∧ (∀ y ∈ W, y ≠ 0) ∧
        (∀ y ∈ W, ‖toE n y‖ ≤ windowC α n) ∧
        (∀ y ∈ W, ‖toE n y‖ + Real.sqrt n / 2 ≤ windowC α n) ∧
        (∀ y ∈ W, 0 < α * ‖toE n y‖) ∧
        (∀ k, k < ParamsAdopted2.numStepsAdopted2 n → k ≠ 0 → ∀ y ∈ W,
          0 < yOf (a0C n) ((k : ℝ) * ParamsAdopted2.stepSizeAdopted2 n) (α * ‖toE n y‖))) :
    ∃ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p) (α R : ℝ)
      (q : (Fin n → ℤ) → EuclideanSpace ℝ (Increments.UT n)) (W : Finset (Fin n → ℤ))
      (A₀ : EuclideanSpace ℝ (Increments.UT n)), RawData p n α R q W A₀ := by
  obtain ⟨p, hp, α, hαpos, hαnorm, hαsmall, hM⟩ :=
    exists_prime_alpha_mul hn (max (2 * winNum n) (max 1 (Real.sqrt n)))
      (le_trans (le_max_left _ _) (le_max_right _ _))
  have hp2 : 2 ≤ p := hp.two_le
  obtain ⟨q, W, A₀, hq, hA₀, hne0, hrad, hwin, hr, hy⟩ := hlat p α hαpos hp2
  exact ⟨p, ⟨hp⟩, ⟨hp.ne_zero⟩, α, (1 - 1 / (n : ℝ)) / α, q, W, A₀,
    rawData_of_lattice hn hαpos hp2 hαnorm hαsmall hM hq hA₀ hne0 hrad hwin hr hy⟩

/-- **HOLE 52**, from `rawData_exists` and brief 60's `tailSideHyp_of_rawData`.  `c` is brief 60's;
it is threaded unchanged.  This is exactly `PaddedLawSetup.tailSide_on_setup`'s hypothesis. -/
theorem hole52_of_tailSideHyp (c : ℝ)
    (hraw : ∀ m : ℕ, Threshold2.n₁ ≤ m →
      ∃ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p) (α R : ℝ)
        (q : (Fin (m + 1) → ℤ) → EuclideanSpace ℝ (Increments.UT (m + 1)))
        (W : Finset (Fin (m + 1) → ℤ)) (A₀ : EuclideanSpace ℝ (Increments.UT (m + 1))),
        RawData p (m + 1) α R q W A₀)
    (htsh : ∀ (m p : ℕ) (α R : ℝ)
      (q : (Fin (m + 1) → ℤ) → EuclideanSpace ℝ (Increments.UT (m + 1)))
      (W : Finset (Fin (m + 1) → ℤ)) (A₀ : EuclideanSpace ℝ (Increments.UT (m + 1))),
      RawData p (m + 1) α R q W A₀ → 3 ≤ m + 1 → TailSideHyp (m + 1) c α q W A₀) :
    ∀ m : ℕ, Threshold2.n₁ ≤ m →
      ∃ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p) (c α R : ℝ)
        (q : (Fin (m + 1) → ℤ) → EuclideanSpace ℝ (Increments.UT (m + 1)))
        (W : Finset (Fin (m + 1) → ℤ)) (A₀ : EuclideanSpace ℝ (Increments.UT (m + 1))),
        3 ≤ m + 1 ∧ RawData p (m + 1) α R q W A₀ ∧ TailSideHyp (m + 1) c α q W A₀ := by
  intro m hm
  obtain ⟨p, hp, hp0, α, R, q, W, A₀, hdata⟩ := hraw m hm
  have h3 : 3 ≤ m + 1 := by
    have : 2073600 ≤ m := by simpa [Threshold2.n₁] using hm
    omega
  exact ⟨p, hp, hp0, c, α, R, q, W, A₀, h3, hdata, htsh m p α R q W A₀ hdata h3⟩

end Submission.L10.RawDataInst

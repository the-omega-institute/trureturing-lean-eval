import Submission.L10.DriftStopped6c
import Submission.L10.Lemma43UniformR2

/-!
# Gate L-10 (`klartag_packing`) — the terminal contact threshold, in units of `n²`

Brief 90 step (b).  Brief 89's `DriftStopped6c.count_ratio_le` and report 85f §(b) differ by
`n²/(8e²) ≈ 7.3·10¹⁰`, the integrated-to-terminal factor.  This module computes the terminal
threshold **from the tree's own definitions** and settles it: it is `Θ(n²)` with an absolute
constant, so the Markov ratio at `c₃''` is `O(1)` and the horizon read stands.

The chain is three identities and two inequalities:

* `C1cR a₀ α n = ρⁿ/(2n) + e^{1/2}·KcR/(n·αⁿ)` (`Lemma43R.C1cR`), so
  `n·αⁿ·C1cR = (α·ρ)ⁿ/2 + e^{1/2}·KcR` — **α-free** (`n_mul_pow_mul_C1cR`), the `KcR` analogue of
  `ThetaTight.n_mul_pow_mul_C1c`;
* `α·ρ ≤ (√a₀)⁻¹ + 1/(4n) ≤ 1` at `a₀ = a0C n` (`ThetaTight.alpha_mul_rhoC_le`), so `(α·ρ)ⁿ ≤ 1`;
* `κ_n = αⁿ·p^{n−1}` (`ChainRaw2RW2.alpha_norm`) and `(p−1)·p^{n−1} ≤ pⁿ − 1`, so `thetaTight`'s
  `p`-dependence is a factor `≤ 1`.

Hence `thetaTight p n (b·C1cR·n²) ≤ 4·b·(1/2 + e^{1/2}·KcR)·n²`.  The one numeric input is
`e^{1/2}·KcR ≤ 826` — `KcR = Kc + 1` with `Kc = e⁶ + e³(2/√(2π) + 2) + 2e³ = 499.797`, so
`e^{1/2}·KcR = 825.675` (report 68's normalised `K = 499.8` is the same constant).
-/

set_option linter.unusedSectionVars false

namespace Submission.L10.TerminalRatio

open Submission.L10 Submission.L10.Increments Submission.L10.Section5

/-! ## 1. The α-free combination at the reach constant -/

variable {a₀ α : ℝ} {n : ℕ}

/-- **`ThetaTight.n_mul_pow_mul_C1c` at `KcR`.**  `C1cR` differs from `C1c` only by `Kc → KcR`, so
the same identity holds and the combination is again α-free. -/
theorem n_mul_pow_mul_C1cR (ha : α ≠ 0) (hn : n ≠ 0) :
    (n : ℝ) * α ^ n * Lemma43R.C1cR a₀ α n
      = (α * rhoC a₀ α n) ^ n / 2 + Real.exp (1 / 2) * Lemma43R.KcR := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hpow : α ^ n ≠ 0 := pow_ne_zero n ha
  rw [Lemma43R.C1cR, mul_pow]
  field_simp

/-- `(α·ρ)ⁿ ≤ 1` at `a₀ = a0C n`: `√(a0C n) = (1 − 1/n)⁻¹`, so `α·ρ ≤ 1 − 3/(4n) < 1`. -/
theorem alpha_mul_rhoC_pow_le (hn : 2073600 ≤ n) (hα : 0 < α)
    (hdef : (n : ℝ) * (α * Real.sqrt n / 2) ≤ 1 / 4) :
    (α * rhoC (a0C n) α n) ^ n ≤ 1 := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hb : (0 : ℝ) < 1 - 1 / (n : ℝ) := by
    have : 1 / (n : ℝ) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hn0 (by norm_num)]; linarith
    linarith
  have hsq : Real.sqrt (a0C n) = (1 - 1 / (n : ℝ))⁻¹ := by
    rw [a0C, show ((1 - 1 / (n : ℝ))⁻¹) ^ 2 = ((1 - 1 / (n : ℝ))⁻¹) ^ 2 from rfl,
      Real.sqrt_sq (by positivity)]
  have hle := ThetaTight.alpha_mul_rhoC_le (a₀ := a0C n) (ne_of_gt hα) (by omega) hdef
  rw [hsq, inv_inv] at hle
  have h1 : α * rhoC (a0C n) α n ≤ 1 := by
    have h4 : 1 / (4 * (n : ℝ)) ≤ 1 / (n : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) hn0]; linarith
    linarith
  have h0 : 0 ≤ α * rhoC (a0C n) α n :=
    mul_nonneg hα.le (rhoC_nonneg hα)
  exact pow_le_one₀ h0 h1

/-! ## 2. `thetaTight` at the terminal constant -/

/-- **The terminal threshold is `Θ(n²)` with an absolute constant.**  `b` is the coefficient the
combined weight gives the terminal summand (`b = 1` for the bare radial bound, `b = 4` once
`ChainRaw3.tailT`'s own factor is counted). -/
theorem thetaTight_terminal_le {p : ℕ} {b : ℝ} (hn : 2073600 ≤ n) (hα : 0 < α) (hb : 0 ≤ b)
    (hdef : (n : ℝ) * (α * Real.sqrt n / 2) ≤ 1 / 4)
    (halpha : α ^ n * ((p ^ (n - 1) : ℕ) : ℝ) = kappa n)
    (hp : 1 ≤ (p : ℝ)) (hpn : 1 ≤ ((p ^ (n - 1) : ℕ) : ℝ)) (hppos : 1 < (p : ℝ) ^ n)
    (hKcR : Real.exp (1 / 2) * Lemma43R.KcR ≤ 826) :
    ThetaTight.thetaTight p n (b * (Lemma43R.C1cR (a0C n) α n * (n : ℝ) ^ 2))
      ≤ 4 * b * 827 * (n : ℝ) ^ 2 := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hd : (0 : ℝ) < (p : ℝ) ^ n - 1 := by linarith
  have hid := n_mul_pow_mul_C1cR (a₀ := a0C n) (ne_of_gt hα) (by omega : n ≠ 0)
  have hpw := alpha_mul_rhoC_pow_le hn hα hdef
  have hcomb : (n : ℝ) * α ^ n * Lemma43R.C1cR (a0C n) α n ≤ 827 := by
    rw [hid]; linarith
  have hcomb0 : 0 ≤ (n : ℝ) * α ^ n * Lemma43R.C1cR (a0C n) α n := by
    have : 0 ≤ Lemma43R.C1cR (a0C n) α n := Lemma43R.C1cR_nonneg hα
    positivity
  -- `thetaTight` unfolded, with `κ_n = αⁿ p^{n-1}`
  have hfac : ((p : ℝ) - 1) * ((p ^ (n - 1) : ℕ) : ℝ) ≤ (p : ℝ) ^ n - 1 := by
    have hnn : n - 1 + 1 = n := by omega
    have hsplit : ((p ^ (n - 1) : ℕ) : ℝ) * (p : ℝ) = (p : ℝ) ^ n := by
      push_cast
      rw [← pow_succ, hnn]
    nlinarith [hpn, hsplit]
  have hkey : ThetaTight.thetaTight p n (b * (Lemma43R.C1cR (a0C n) α n * (n : ℝ) ^ 2))
      = (4 * b * (n : ℝ) ^ 2 * ((n : ℝ) * α ^ n * Lemma43R.C1cR (a0C n) α n))
        * ((((p : ℝ) - 1) * ((p ^ (n - 1) : ℕ) : ℝ)) / ((p : ℝ) ^ n - 1)) := by
    rw [ThetaTight.thetaTight, ← halpha]
    field_simp
  rw [hkey]
  have hratio : (((p : ℝ) - 1) * ((p ^ (n - 1) : ℕ) : ℝ)) / ((p : ℝ) ^ n - 1) ≤ 1 := by
    rw [div_le_one hd]; exact hfac
  have hratio0 : 0 ≤ (((p : ℝ) - 1) * ((p ^ (n - 1) : ℕ) : ℝ)) / ((p : ℝ) ^ n - 1) := by
    apply div_nonneg _ hd.le
    have : (0 : ℝ) ≤ (p : ℝ) - 1 := by linarith
    positivity
  have hA0 : 0 ≤ 4 * b * (n : ℝ) ^ 2 * ((n : ℝ) * α ^ n * Lemma43R.C1cR (a0C n) α n) := by
    positivity
  have hA : 4 * b * (n : ℝ) ^ 2 * ((n : ℝ) * α ^ n * Lemma43R.C1cR (a0C n) α n)
      ≤ 4 * b * 827 * (n : ℝ) ^ 2 := by nlinarith [hcomb, hb, sq_nonneg ((n : ℝ))]
  nlinarith [hA, hA0, hratio, hratio0]

/-! ## 3. The Markov ratio -/

/-- **The count failure at `c₃''`, settled.**  At `b = 4` (the reading that counts
`ChainRaw3.tailT`'s own factor) the bound is `2·13 232/50 653 = 0.522`; at `b = 1` it is `0.131`.
Either way it is `O(1)` — **not** the `1.76·10¹⁰` of report 85f §(b). -/
theorem count_ratio_terminal {θT b : ℝ} (hn : 2073600 ≤ n) (hb : 0 ≤ b)
    (hθ : θT ≤ 4 * b * 827 * (n : ℝ) ^ 2) :
    (2 * θT + 0) / DriftStopped6c.c3Adopted'' n ≤ 2 * (4 * b * 827) / 50653 :=
  DriftStopped6c.count_ratio_le hn (by positivity) hθ

end Submission.L10.TerminalRatio

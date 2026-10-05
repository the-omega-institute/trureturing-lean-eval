import Submission.L10.TerminalCount

/-!
# Gate L-10 (`klartag_packing`) — the `θ` normalisation, and the α-free constant behind it

Brief 77 (hinge).  `Params.theta` is set to `16·C` (`TailAtStep.params_of_raw2`), i.e. `64·C1C α n`,
while the only thing `Params.markov` actually needs is `θ > 2(p−1)·n·κ_n·C/(pⁿ−1)`.  The two differ
by `α⁻ⁿ/n`, which at the tiling defect's own bound `α ≤ 1/(2n^{3/2})` is at least `e^{4.7·10⁷}` at
the threshold dimension.  The consequence is that every consumer of `theta` — `LightContact`, and
`StateInvariant4.measureReal_compl_countGood_le_expected`'s `(2θ+E)/c₃` — is vacuous as stated.

**The reason the tight threshold is computable at all** is the identity below: `C1c` is `Θ(α⁻ⁿ/n)`,
and the combination `n·αⁿ·C1c` that `markov` forms against `κ_n = αⁿ·p^{n−1}` is **α-free up to the
tiling defect**:

  `n·αⁿ·C1c a₀ α n = (α·ρ)ⁿ/2 + e^{1/2}·K`,  `α·ρ = (√a₀)⁻¹ + α√n/2 ∈ [1 − 1/n, 1 − 3/(4n)]`,

so it lies in `[824.210, 824.262]` at every `n ≥ n₁` and every admissible `α`.  The report has the
budgets that follow.  `TerminalCount.lean` is reported and is not edited; this module imports it.
-/

set_option linter.unusedSectionVars false

namespace Submission.L10.ThetaTight

open Submission.L10 Submission.L10.Increments Submission.L10.Section5

variable {a₀ α : ℝ} {n : ℕ}

/-- `α·ρ = (√a₀)⁻¹ + α√n/2` — the α-dependence of `ρ` is exactly one factor of `α⁻¹`. -/
theorem alpha_mul_rhoC (ha : α ≠ 0) :
    α * rhoC a₀ α n = (Real.sqrt a₀)⁻¹ + α * Real.sqrt n / 2 := by
  rw [rhoC]
  field_simp

/-- **The α-free combination.**  `C1c` carries exactly one factor `α⁻ⁿ/n`, and `markov` forms it
against `κ_n = αⁿ·p^{n−1}`, so the threshold it needs depends on `α` only through `α·ρ`. -/
theorem n_mul_pow_mul_C1c (ha : α ≠ 0) (hn : n ≠ 0) :
    (n : ℝ) * α ^ n * C1c a₀ α n = (α * rhoC a₀ α n) ^ n / 2 + Real.exp (1 / 2) * Kc := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hpow : α ^ n ≠ 0 := pow_ne_zero n ha
  rw [C1c, mul_pow]
  field_simp

/-- The upper end of `α·ρ`, from the tiling defect `n·(α√n/2) ≤ 1/4`. -/
theorem alpha_mul_rhoC_le (ha : α ≠ 0) (hn : n ≠ 0)
    (hdef : (n : ℝ) * (α * Real.sqrt n / 2) ≤ 1 / 4) :
    α * rhoC a₀ α n ≤ (Real.sqrt a₀)⁻¹ + 1 / (4 * (n : ℝ)) := by
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  rw [alpha_mul_rhoC ha]
  have h : α * Real.sqrt n / 2 ≤ 1 / (4 * (n : ℝ)) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hdef, hnR]
  linarith

/-- **The tight threshold.**  `Params.markov` asks for `2(p−1)·n·κ_n·C < θ·(pⁿ−1)`; this is the
smallest `θ` that meets it, written out.  Unlike `16·C` it is `α`-free to within the tiling
defect, because `n·κ_n·C1c = p^{n−1}·(n·αⁿ·C1c)`. -/
noncomputable def thetaTight (p n : ℕ) (C : ℝ) : ℝ :=
  4 * ((p : ℝ) - 1) * (n : ℝ) * kappa n * C / ((p : ℝ) ^ n - 1)

/-- `thetaTight` clears `markov`'s bound with a factor of two to spare. -/
theorem two_mul_lt_thetaTight_mul {p : ℕ} {C : ℝ} (hp : 1 < (p : ℝ) ^ n)
    (hC : 0 < ((p : ℝ) - 1) * (n : ℝ) * kappa n * C) :
    2 * (((p : ℝ) - 1) * (n : ℝ) * kappa n * C)
      < thetaTight p n C * ((p : ℝ) ^ n - 1) := by
  have hd : (0 : ℝ) < (p : ℝ) ^ n - 1 := by linarith
  rw [thetaTight, div_mul_cancel₀ _ (ne_of_gt hd)]
  linarith

end Submission.L10.ThetaTight

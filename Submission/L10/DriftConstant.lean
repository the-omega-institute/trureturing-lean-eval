import Submission.L10.ThetaTight

/-!
# Gate L-10 (`klartag_packing`) — the drift's loss is a constant, and it pays in `C'`

Brief 80.  **Report 77 §2 and §4 compared the wrong two numbers and its drift verdict is wrong.**
It asked whether `∑_{W_g} intWeight` fits inside `T·dim`, i.e. whether the drift's `S` is positive.
`S` does not have to be positive.  The target is
`Theorem4.DriftSide'''`'s `logDet A ≤ C' − 4·log(m+1)` with **`C'` a free real** — `c₀ = exp(−C'/2)`
and the challenge asks only for *some* `c > 0` — so a loss that is **uniform in `n`** is paid once,
in the constant, and the `n²` of the theorem is untouched.

And the loss is uniform: `ThetaTight.n_mul_pow_mul_C1c` says `n·αⁿ·C1c` is α-free **and n-free**, so
the tight threshold `θ' = 64e²·(n·αⁿ·C1c) ≈ 3.898·10⁵` carries no `n` at all.

## The decomposition

With `κ = c·h`, `h·N = T` and `sum_free_ge`'s `S ≥ N·dim − Θ/h` (`Θ := ∑_{W_g} intWeight`),

  `κ·S ≥ c·T·dim − c·Θ`   (`kappa_mul_S_ge`)

so `DriftStopped6.drift_bound_stopped_maximal` gives

  `∫ logDet_m + 4·log(m+1) ≤ D₀ + c·Θ + (4·log(m+1) − c·T·dim) + E`   (`logDet_target_of_drift`)

with `E = dim·ε + C₁·2B`.  Since `T·dim = 8 log n`, the middle bracket is `4 log n·(1 − 2c)`, and
`c → 1/2`, so it is `≈ 192·(log n)^{3/2}/√n` — decreasing, `7.40` at `n₁`.  Every other term is
uniformly bounded; the report has the table.  `Cprime` names the sum and `Cprime_le` bounds it from
the six term bounds, so the table is auditable term by term.

`ThetaTight.lean` is reported and is not edited; this module imports it.
-/

set_option linter.unusedSectionVars false

namespace Submission.L10.DriftConstant

open Submission.L10 Submission.L10.Increments

/-! ## 1. The loss is a constant -/

/-- **`sum_free_ge`, priced.**  A lower bound on the summed free dimension of the shape
`ContactIntegrated.sum_free_ge` produces `κ·S ≥ c·T·dim − c·Θ`: the contact total enters the drift
**once**, scaled by `c`, and not per step. -/
theorem kappa_mul_S_ge {c h T dd Θ S : ℝ} {N : ℕ} (hc : 0 ≤ c) (hh : 0 < h)
    (hT : (N : ℝ) * h = T) (hS : (N : ℝ) * dd - Θ / h ≤ S) :
    c * (T * dd) - c * Θ ≤ (c * h) * S := by
  have hmul : (c * h) * ((N : ℝ) * dd - Θ / h) ≤ (c * h) * S :=
    mul_le_mul_of_nonneg_left hS (by positivity)
  have hval : (c * h) * ((N : ℝ) * dd - Θ / h) = c * (((N : ℝ) * h) * dd) - c * Θ := by
    field_simp
  rw [hval, hT] at hmul
  exact hmul

/-- **The target, from the drift bound.**  `4·log(m+1)` is moved to the left and the loss `c·Θ` to
the right; nothing here is an estimate, it is the decomposition the report's table audits. -/
theorem logDet_target_of_drift {c h T dd Θ S D0 Dm E L : ℝ} {N : ℕ}
    (hc : 0 ≤ c) (hh : 0 < h) (hT : (N : ℝ) * h = T)
    (hS : (N : ℝ) * dd - Θ / h ≤ S)
    (hdrift : Dm ≤ D0 - (c * h) * S + E) :
    Dm + L ≤ D0 + c * Θ + (L - c * (T * dd)) + E := by
  have hkS := kappa_mul_S_ge hc hh hT hS
  linarith

/-! ## 2. `C'` in closed form -/

/-- **`C'`, term by term.**  `D₀ = n·log a₀`; `c·Θ` the uniform loss; `resid = 4 log n·(1 − 2c)`
the uncancelled part of eq. (68)'s `4 log n`; `dim·ε`; `C₁·2B`; and the slack the pigeonhole pays to
land inside `wiredGood'`. -/
noncomputable def Cprime (D0 loss resid err slackB exist : ℝ) : ℝ :=
  D0 + loss + resid + err + slackB + exist

/-- **The audit.**  Each term bounded separately bounds `C'`, so the report's table is the proof. -/
theorem Cprime_le {D0 loss resid err slackB exist b₁ b₂ b₃ b₄ b₅ b₆ : ℝ}
    (h1 : D0 ≤ b₁) (h2 : loss ≤ b₂) (h3 : resid ≤ b₃) (h4 : err ≤ b₄)
    (h5 : slackB ≤ b₅) (h6 : exist ≤ b₆) :
    Cprime D0 loss resid err slackB exist ≤ b₁ + b₂ + b₃ + b₄ + b₅ + b₆ := by
  rw [Cprime]
  linarith

/-- **The residual term is `4 log n·(1 − 2c)` and it is nonnegative**, because the drift's quadratic
coefficient never exceeds `1/2` (`DriftStopped7.cAdopted_le_half`).  It is the only term carrying an
`n` that does not obviously vanish, and the report measures it at `192·(log n)^{3/2}/√n`. -/
theorem resid_nonneg {n : ℕ} (hn : 2073600 ≤ n) (hlog : 0 ≤ Real.log n) :
    0 ≤ 4 * Real.log n * (1 - 2 * DriftStopped6.cAdopted n) := by
  have h := DriftStopped7.cAdopted_le_half hn
  have h2 : 0 ≤ 1 - 2 * DriftStopped6.cAdopted n := by linarith
  exact mul_nonneg (by linarith) h2

/-- **The loss is at most `θ'/2`**, uniformly in `n` and `α`, since `c ≤ 1/2`. -/
theorem loss_le_half {n : ℕ} (hn : 2073600 ≤ n) {θ : ℝ} (hθ : 0 ≤ θ) :
    DriftStopped6.cAdopted n * θ ≤ θ / 2 := by
  have h := DriftStopped7.cAdopted_le_half hn
  nlinarith [h, hθ]

end Submission.L10.DriftConstant

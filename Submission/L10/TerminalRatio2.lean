import Submission.L10.TerminalRatio
import Submission.L10.ExpBounds
import Submission.L10.SlackDecay

/-!
# Gate L-10 (`klartag_packing`) — the terminal count, with its last constant discharged

`TerminalRatio.thetaTight_terminal_le` left one numeric binder open,
`hKcR : Real.exp (1/2) * Lemma43R.KcR ≤ 826`.  Brief 92's `ExpBounds.exp_half_mul_KcR_le` proves
it (measured `825.674 5`, slack `0.267`), so the terminal threshold is now unconditional, and the
decaying Markov ratio of `SlackDecay` applies to it directly.
-/

set_option linter.unusedSectionVars false

namespace Submission.L10.TerminalRatio2

open Submission.L10 Submission.L10.Increments Submission.L10.Section5

variable {a₀ α : ℝ} {n : ℕ}

/-- **`TerminalRatio.thetaTight_terminal_le`, unconditional.** -/
theorem thetaTight_terminal_le' {p : ℕ} {b : ℝ} (hn : 2073600 ≤ n) (hα : 0 < α) (hb : 0 ≤ b)
    (hdef : (n : ℝ) * (α * Real.sqrt n / 2) ≤ 1 / 4)
    (halpha : α ^ n * ((p ^ (n - 1) : ℕ) : ℝ) = kappa n)
    (hp : 1 ≤ (p : ℝ)) (hpn : 1 ≤ ((p ^ (n - 1) : ℕ) : ℝ)) (hppos : 1 < (p : ℝ) ^ n) :
    ThetaTight.thetaTight p n (b * (Lemma43R.C1cR (a0C n) α n * (n : ℝ) ^ 2))
      ≤ 4 * b * 827 * (n : ℝ) ^ 2 :=
  TerminalRatio.thetaTight_terminal_le hn hα hb hdef halpha hp hpn hppos
    ExpBounds.exp_half_mul_KcR_le

/-- **The count failure at `c₃''`, unconditional and decaying.**  At `b = 4` the constant is
`K = 4·4·827 = 13 232`, so the ratio is `≤ 2·13 232/s³` with `s = √(√n)` — `0.522` at the
threshold and `→ 0`. -/
theorem count_ratio_terminal' {θT b : ℝ} (hn : 2073600 ≤ n) (hb : 0 ≤ b)
    (hθ : θT ≤ 4 * b * 827 * (n : ℝ) ^ 2) :
    (2 * θT + 0) / FinalDischarge2.c3Adopted'' n
      ≤ 2 * (4 * b * 827) / Real.sqrt (Real.sqrt (n : ℝ)) ^ 3 :=
  SlackDecay.count_ratio_decay hn (by positivity) hθ

/-- **The existence slack at the terminal threshold**, uniform: `≤ 19·(4·b·827)`. -/
theorem slack_terminal {θT b : ℝ} (hn : 2073600 ≤ n) (hb : 0 ≤ b) (hθ0 : 0 ≤ θT)
    (hθ : θT ≤ 4 * b * 827 * (n : ℝ) ^ 2) :
    (n : ℝ) * (DriftStopped6.r0Adopted n
        + FinalDischarge2.c3Adopted'' n * DriftStopped6.etaAdopted n)
        * ((2 * θT + 0) / FinalDischarge2.c3Adopted'' n)
      ≤ 19 * (4 * b * 827) :=
  SlackDecay.slack_uniform hn (by positivity) hθ0 hθ

end Submission.L10.TerminalRatio2

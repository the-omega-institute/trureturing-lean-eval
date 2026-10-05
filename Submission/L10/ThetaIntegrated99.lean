import Submission.L10.TerminalRatio2
import Submission.L10.TailAtStepR5W2

/-!
# Gate L-10 (`klartag_packing`), brief 99 — the integrated threshold at `B = 0`, priced

The second half of the repair report `99-final-theorem.md` §3 describes.  With the terminal
coefficient `B` set to `0` the combined weight is `wComb A 0 = A·wProf`, its threshold is
`θ3 A 0 p m α = thetaTight p (m+1) (A·C4)`, and `TailAtStepR5W2.sums_split`'s `h₁` is met by
`Θ = thetaTight p (m+1) (C4)` — with **no `n` in it**, which is what `hbudget` needs and what the
`(B/A)·4·λ·C1cR·n²` cross term destroys at any `B > 0`.

`TerminalRatio2.thetaTight_terminal_le'` is stated for the argument `b·(C1cR·n²)` at a free `b`, so
it prices `C4` too: `C4 = 4·e²·C1cR·(8 − 8/n²)` is that shape at `b = 4·e²·(8 − 8/n²)/n²`, giving

```
thetaTight p n (C3 n 1 0 α)  ≤  4·b·827·n²  =  13 232·e²·(8 − 8/n²)  ≤  105 856·e²  <  8·10⁵
```

— report 80 §2's `θ' = 3.897 68·10⁵` is the same constant at its exact value (that report's `c·θ'`
is the budget's `cqAt·Θ`, and `c ≤ 1/2`).  Every hypothesis is in `hline`'s context:
`tiling_defect` and `alpha_norm` are fields of `PaddedLawSetupRW2.RawDataR` (`:57`, `:53`), and
`1 ≤ p`, `1 ≤ p^{n-1}`, `1 < pⁿ` follow from `Fact (Nat.Prime p)`.

Nothing reported is edited.
-/

set_option linter.unusedSectionVars false

namespace Submission.L10.ThetaIntegrated99

open Submission.L10 Submission.L10.Increments Submission.L10.Section5

variable {n : ℕ} {α : ℝ}

/-- `C3 n 1 0 α` is `TerminalRatio2`'s argument shape at `b = 4·e²·(8 − 8/n²)/n²`. -/
theorem C3_eq_terminal_form (hn : 2 ≤ n) :
    TailAtStepR5W2.C3 n 1 0 α
      = (4 * Real.exp 2 * (8 - 8 / (n : ℝ) ^ 2) / (n : ℝ) ^ 2)
        * (Lemma43R.C1cR (a0C n) α n * (n : ℝ) ^ 2) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hne : ((n : ℝ)) ≠ 0 := ne_of_gt hn0
  rw [TailAtStepR5W2.C3, Lemma43R.C1R]
  field_simp
  ring

/-- `e² ≤ 7.4`. -/
theorem exp_two_le : Real.exp 2 ≤ 7.4 := by
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  have h0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  nlinarith [he, h0]

/-- **The integrated threshold at `B = 0` is below `8·10⁵`, uniformly in `n`, `p` and `α`.** -/
theorem theta3_integrated_le {p : ℕ} (hn : 2073600 ≤ n) (hα : 0 < α)
    (hdef : (n : ℝ) * (α * Real.sqrt n / 2) ≤ 1 / 4)
    (halpha : α ^ n * ((p ^ (n - 1) : ℕ) : ℝ) = kappa n)
    (hp : 1 ≤ (p : ℝ)) (hpn : 1 ≤ ((p ^ (n - 1) : ℕ) : ℝ)) (hppos : 1 < (p : ℝ) ^ n) :
    ThetaTight.thetaTight p n (TailAtStepR5W2.C3 n 1 0 α) ≤ 800000 := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hsq : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  have height : (0 : ℝ) < 8 - 8 / (n : ℝ) ^ 2 := Lemma43R.eight_sub_pos (by omega)
  have hb0 : (0 : ℝ) ≤ 4 * Real.exp 2 * (8 - 8 / (n : ℝ) ^ 2) / (n : ℝ) ^ 2 := by
    have := Real.exp_pos 2
    positivity
  rw [C3_eq_terminal_form (by omega)]
  refine le_trans (TerminalRatio2.thetaTight_terminal_le' (p := p) hn hα hb0 hdef halpha
    hp hpn hppos) ?_
  have hid : 4 * (4 * Real.exp 2 * (8 - 8 / (n : ℝ) ^ 2) / (n : ℝ) ^ 2) * 827 * (n : ℝ) ^ 2
      = 13232 * Real.exp 2 * (8 - 8 / (n : ℝ) ^ 2) := by
    field_simp
    ring
  rw [hid]
  have hle8 : 8 - 8 / (n : ℝ) ^ 2 ≤ 8 := by
    have : (0 : ℝ) ≤ 8 / (n : ℝ) ^ 2 := by positivity
    linarith
  have hex := exp_two_le
  have hex0 : (0 : ℝ) < Real.exp 2 := Real.exp_pos 2
  nlinarith [hex, hex0, hle8, height]

end Submission.L10.ThetaIntegrated99

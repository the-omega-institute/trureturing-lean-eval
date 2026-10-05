import Submission.L10.DriftStopped6d
import Submission.L10.TerminalRatio

/-!
# Gate L-10 (`klartag_packing`) — the existence slack decays, with no lower bound on `η`

Brief 90.  Report `82a-c3-uniform.md` §2 asked for `c₃·η ≫ √(log n/n)` to keep the existence slack
bounded.  **That is not a theorem** — the tree has no *lower* bound on `η` — and it is not needed:
`c3Adopted''` is `n³/√(√n)`, so the Markov ratio has an explicit decay

  `P ≤ 2·θ_T/c₃'' ≤ 2K·n²/c₃'' = 2K/s³`,   `s := √(√n)`, `s⁴ = n`,

which is pure algebra from the definition (`count_ratio_decay`).  The shift `|L| = n·|log (mAt)|`
is at most `2·n·(r₀ + c₃''·η)` and each half is beaten by `1/s³`:

  `n·r₀·(2K/s³) = 48K·√(log n)/s`   (`r₀ = 24√(log n/n)`, `√n = s²`),
  `n·c₃''·η·(2K/s³) ≤ 2√2·K`        (`c₃''·η ≤ √2/s`, `n = s⁴`),

so the product is bounded **uniformly**, by `19·K` (`slack_uniform`), using only
`DriftStopped7.log_le_four_sqrt_sqrt` and `sqrt_sqrt_ge`.  `DriftStopped6c.count_ratio_le`'s
constant form `2K/50 653` is true but too weak for this: it does not decay, and `|L|` grows like
`24√(n log n)`.
-/

set_option linter.unusedSectionVars false

namespace Submission.L10.SlackDecay

open Submission.L10 Submission.L10.Increments

variable {n : ℕ}

/-! ## 1. Pure algebra in `s` (rule 19: the inequalities, away from the `√`s) -/

theorem ratio_algebra {s θT K : ℝ} (hs : 0 < s) (_hK : 0 ≤ K) (hθ : θT ≤ K * s ^ 8) :
    (2 * θT + 0) / s ^ 11 ≤ 2 * K / s ^ 3 := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hmul := mul_le_mul_of_nonneg_right hθ (pow_pos hs 3).le
  have hid : K * s ^ 8 * s ^ 3 = K * s ^ 11 := by ring
  rw [hid] at hmul
  linarith

theorem slack_algebra {s A P R K : ℝ} (hs : 0 < s) (_hK : 0 ≤ K) (hR : 0 ≤ R)
    (hA : A ≤ 24 * R * s ^ 2 + Real.sqrt 2 * s ^ 3) (_hA0 : 0 ≤ A)
    (hP : P ≤ 2 * K / s ^ 3) (hP0 : 0 ≤ P) :
    A * P ≤ 48 * K * (R / s) + 2 * Real.sqrt 2 * K := by
  have hs3 : (0 : ℝ) < s ^ 3 := pow_pos hs 3
  have hbase : (0 : ℝ) ≤ 24 * R * s ^ 2 + Real.sqrt 2 * s ^ 3 := by positivity
  have h1 : A * P ≤ (24 * R * s ^ 2 + Real.sqrt 2 * s ^ 3) * (2 * K / s ^ 3) := by
    have := mul_le_mul hA hP hP0 hbase
    linarith
  have h2 : (24 * R * s ^ 2 + Real.sqrt 2 * s ^ 3) * (2 * K / s ^ 3)
      = 48 * K * (R / s) + 2 * Real.sqrt 2 * K := by
    field_simp
    ring
  linarith [h1, h2.le, h2.ge]

/-! ## 2. `s = √(√n)`: its powers, and `c₃'' = s¹¹` -/

theorem sq_sqrt_sqrt (_hn : 0 ≤ (n : ℝ)) :
    Real.sqrt (Real.sqrt (n : ℝ)) ^ 2 = Real.sqrt (n : ℝ) :=
  Real.sq_sqrt (Real.sqrt_nonneg _)

theorem pow_four_sqrt_sqrt (hn : 0 ≤ (n : ℝ)) :
    Real.sqrt (Real.sqrt (n : ℝ)) ^ 4 = (n : ℝ) := by
  have h : Real.sqrt (Real.sqrt (n : ℝ)) ^ 4
      = (Real.sqrt (Real.sqrt (n : ℝ)) ^ 2) ^ 2 := by ring
  rw [h, sq_sqrt_sqrt hn, Real.sq_sqrt hn]

theorem sqrt_sqrt_pos (hn : 2073600 ≤ n) : 0 < Real.sqrt (Real.sqrt (n : ℝ)) := by
  have := DriftStopped7.sqrt_sqrt_ge hn; linarith

/-- `c3Adopted'' n = n³/s = s¹¹`. -/
theorem c3_eq_pow (hn : 2073600 ≤ n) :
    FinalDischarge2.c3Adopted'' n = Real.sqrt (Real.sqrt (n : ℝ)) ^ 11 := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hs := sqrt_sqrt_pos hn
  have hs4 := pow_four_sqrt_sqrt (n := n) hn0.le
  rw [FinalDischarge2.c3Adopted'', div_eq_iff (ne_of_gt hs)]
  calc (n : ℝ) ^ 3 = (Real.sqrt (Real.sqrt (n : ℝ)) ^ 4) ^ 3 := by rw [hs4]
    _ = Real.sqrt (Real.sqrt (n : ℝ)) ^ 11 * Real.sqrt (Real.sqrt (n : ℝ)) := by ring

/-! ## 3. The Markov ratio decays like `s⁻³` -/

/-- **The decaying form**, needing no lower bound on `η`: `n²/c₃'' = 1/s³` is pure algebra. -/
theorem count_ratio_decay {θT K : ℝ} (hn : 2073600 ≤ n) (hK : 0 ≤ K)
    (hθ : θT ≤ K * (n : ℝ) ^ 2) :
    (2 * θT + 0) / FinalDischarge2.c3Adopted'' n
      ≤ 2 * K / Real.sqrt (Real.sqrt (n : ℝ)) ^ 3 := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hs := sqrt_sqrt_pos hn
  have hs4 := pow_four_sqrt_sqrt (n := n) hn0.le
  have hnsq : (n : ℝ) ^ 2 = Real.sqrt (Real.sqrt (n : ℝ)) ^ 8 := by
    calc (n : ℝ) ^ 2 = (Real.sqrt (Real.sqrt (n : ℝ)) ^ 4) ^ 2 := by rw [hs4]
      _ = Real.sqrt (Real.sqrt (n : ℝ)) ^ 8 := by ring
  rw [c3_eq_pow hn]
  exact ratio_algebra hs hK (by rw [← hnsq]; exact hθ)

/-! ## 4. The shift, and the uniform slack -/

theorem shift_le (hn : 2073600 ≤ n) :
    (n : ℝ) * (DriftStopped6.r0Adopted n
        + FinalDischarge2.c3Adopted'' n * DriftStopped6.etaAdopted n)
      ≤ 24 * Real.sqrt (Real.log n) * Real.sqrt (Real.sqrt (n : ℝ)) ^ 2
        + Real.sqrt 2 * Real.sqrt (Real.sqrt (n : ℝ)) ^ 3 := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hs := sqrt_sqrt_pos hn
  have hs2 := sq_sqrt_sqrt (n := n) hn0.le
  have hs4 := pow_four_sqrt_sqrt (n := n) hn0.le
  have h1 : (n : ℝ) * DriftStopped6.r0Adopted n
      = 24 * Real.sqrt (Real.log n) * Real.sqrt (Real.sqrt (n : ℝ)) ^ 2 := by
    rw [DriftStopped6.r0Adopted, Real.sqrt_div' _ hn0.le, hs2]
    rw [show (n : ℝ) * (24 * (Real.sqrt (Real.log n) / Real.sqrt (n : ℝ)))
      = 24 * Real.sqrt (Real.log n) * ((n : ℝ) / Real.sqrt (n : ℝ)) by ring,
      Real.div_sqrt]
  have hce : FinalDischarge2.c3Adopted'' n * DriftStopped6.etaAdopted n
      ≤ Real.sqrt 2 / Real.sqrt (Real.sqrt (n : ℝ)) := by
    have heta : DriftStopped6.etaAdopted n ≤ Real.sqrt 2 / (n : ℝ) ^ 3 := by
      rw [DriftStopped6.etaAdopted]; exact ParamsAdopted2.eta2_le (by omega)
    have hc0 : 0 ≤ FinalDischarge2.c3Adopted'' n := FinalDischarge2.c3Adopted''_nonneg n
    have hstep := mul_le_mul_of_nonneg_left heta hc0
    have hval : FinalDischarge2.c3Adopted'' n * (Real.sqrt 2 / (n : ℝ) ^ 3)
        = Real.sqrt 2 / Real.sqrt (Real.sqrt (n : ℝ)) := by
      rw [FinalDischarge2.c3Adopted'']; field_simp
    rwa [hval] at hstep
  have h2 : (n : ℝ) * (FinalDischarge2.c3Adopted'' n * DriftStopped6.etaAdopted n)
      ≤ Real.sqrt 2 * Real.sqrt (Real.sqrt (n : ℝ)) ^ 3 := by
    have hmul := mul_le_mul_of_nonneg_left hce hn0.le
    have heq : (n : ℝ) * (Real.sqrt 2 / Real.sqrt (Real.sqrt (n : ℝ)))
        = Real.sqrt 2 * Real.sqrt (Real.sqrt (n : ℝ)) ^ 3 := by
      calc (n : ℝ) * (Real.sqrt 2 / Real.sqrt (Real.sqrt (n : ℝ)))
          = Real.sqrt 2 * ((n : ℝ) / Real.sqrt (Real.sqrt (n : ℝ))) := by ring
        _ = Real.sqrt 2 * (Real.sqrt (Real.sqrt (n : ℝ)) ^ 4
              / Real.sqrt (Real.sqrt (n : ℝ))) := by rw [hs4]
        _ = Real.sqrt 2 * Real.sqrt (Real.sqrt (n : ℝ)) ^ 3 := by
              rw [show Real.sqrt (Real.sqrt (n : ℝ)) ^ 4
                = Real.sqrt (Real.sqrt (n : ℝ)) ^ 3 * Real.sqrt (Real.sqrt (n : ℝ)) by ring,
                mul_div_assoc, div_self (ne_of_gt hs), mul_one]
    rwa [heq] at hmul
  nlinarith [h1, h2]

/-- **The slack, with the decay applied.** -/
theorem slack_le {θT K : ℝ} (hn : 2073600 ≤ n) (hK : 0 ≤ K) (hθ0 : 0 ≤ θT)
    (hθ : θT ≤ K * (n : ℝ) ^ 2) :
    (n : ℝ) * (DriftStopped6.r0Adopted n
        + FinalDischarge2.c3Adopted'' n * DriftStopped6.etaAdopted n)
        * ((2 * θT + 0) / FinalDischarge2.c3Adopted'' n)
      ≤ 48 * K * (Real.sqrt (Real.log n) / Real.sqrt (Real.sqrt (n : ℝ)))
        + 2 * Real.sqrt 2 * K := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hs := sqrt_sqrt_pos hn
  have hc0 : 0 < FinalDischarge2.c3Adopted'' n := DriftStopped6d.c3_pos (by omega)
  have hP := count_ratio_decay hn hK hθ
  have hP0 : 0 ≤ (2 * θT + 0) / FinalDischarge2.c3Adopted'' n :=
    div_nonneg (by linarith) hc0.le
  have hA0 : (0 : ℝ) ≤ (n : ℝ) * (DriftStopped6.r0Adopted n
      + FinalDischarge2.c3Adopted'' n * DriftStopped6.etaAdopted n) := by
    have h1 : (0 : ℝ) ≤ DriftStopped6.r0Adopted n := DriftStopped7.r0Adopted_nonneg
    have h2 : (0 : ℝ) ≤ FinalDischarge2.c3Adopted'' n * DriftStopped6.etaAdopted n :=
      mul_nonneg (FinalDischarge2.c3Adopted''_nonneg n)
        (DriftStopped7.etaAdopted_nonneg (n := n))
    positivity
  exact slack_algebra hs hK (Real.sqrt_nonneg _) (shift_le hn) hA0 hP hP0

/-- **The uniform bound.**  `√(log n) ≤ 2√s` (`DriftStopped7.log_le_four_sqrt_sqrt`) and `s ≥ 37`
give `√(log n)/s ≤ 2/√s ≤ 1/3`, so the slack never exceeds `19·K` — no `η` lower bound anywhere. -/
theorem slack_uniform {θT K : ℝ} (hn : 2073600 ≤ n) (hK : 0 ≤ K) (hθ0 : 0 ≤ θT)
    (hθ : θT ≤ K * (n : ℝ) ^ 2) :
    (n : ℝ) * (DriftStopped6.r0Adopted n
        + FinalDischarge2.c3Adopted'' n * DriftStopped6.etaAdopted n)
        * ((2 * θT + 0) / FinalDischarge2.c3Adopted'' n)
      ≤ 19 * K := by
  have hs := sqrt_sqrt_pos hn
  have hs37 := DriftStopped7.sqrt_sqrt_ge hn
  have hlog : Real.log n ≤ 4 * Real.sqrt (Real.sqrt (n : ℝ)) :=
    DriftStopped7.log_le_four_sqrt_sqrt (by omega)
  have hsl : Real.sqrt (Real.log n)
      ≤ 2 * Real.sqrt (Real.sqrt (Real.sqrt (n : ℝ))) := by
    have h := Real.sqrt_le_sqrt hlog
    rwa [show (4 : ℝ) * Real.sqrt (Real.sqrt (n : ℝ))
      = 2 ^ 2 * Real.sqrt (Real.sqrt (n : ℝ)) by ring,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)] at h
  have hrs : (6 : ℝ) ≤ Real.sqrt (Real.sqrt (Real.sqrt (n : ℝ))) := by
    have h36 : (36 : ℝ) ≤ Real.sqrt (Real.sqrt (n : ℝ)) := by linarith
    have h := Real.sqrt_le_sqrt h36
    rwa [show (36 : ℝ) = 6 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at h
  have hss : Real.sqrt (Real.sqrt (Real.sqrt (n : ℝ)))
      * Real.sqrt (Real.sqrt (Real.sqrt (n : ℝ))) = Real.sqrt (Real.sqrt (n : ℝ)) :=
    Real.mul_self_sqrt (Real.sqrt_nonneg _)
  have hratio : Real.sqrt (Real.log n) / Real.sqrt (Real.sqrt (n : ℝ)) ≤ 1 / 3 := by
    rw [div_le_div_iff₀ hs (by norm_num)]
    nlinarith [hsl, hrs, hss]
  have h2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [show (3 : ℝ) / 2 = Real.sqrt ((3 / 2) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hmain := slack_le hn hK hθ0 hθ
  nlinarith [hmain, hratio, h2, hK]

end Submission.L10.SlackDecay

/-
Gate L-10 (`klartag_packing`), brief 31.

**Lemma 4.3's instantiation at `Params'`.**  `hgbound_chained` (report 28) produces the constant
`ρⁿ/(2n) + (e^{1/2}/(n·αⁿ))·K·e^{n²t/8}`, while `Lemma43C.weight_bound_of_chain` consumes bounds of
the shape `C₁·e^{n²t/8}`.  The two differ by where the inner-ball term sits, and
`const_normalise` moves it — using only `e^{n²t/8} ≥ 1`.
-/
import Submission.L10.Lemma43Params

namespace Submission.L10

open MeasureTheory Set Real
open scoped ENNReal NNReal

/-! ## 1. The constant, normalised into `weight_bound_of_chain`'s shape -/

/-- **`hgbound_chained`'s constant in `C₁·e^{n²t/8}` form.**  The inner-ball term `ρⁿ/(2n)` is a
constant, not a multiple of the exponential; since `e^{n²t/8} ≥ 1` it may be absorbed into `C₁`. -/
theorem const_normalise {ρ A t : ℝ} {n : ℕ} (hρ : 0 ≤ ρ) (ht : 0 ≤ t) :
    ρ ^ n / (2 * n) + A * Real.exp ((n : ℝ) ^ 2 * t / 8)
      ≤ (ρ ^ n / (2 * n) + A) * Real.exp ((n : ℝ) ^ 2 * t / 8) := by
  have he : (1 : ℝ) ≤ Real.exp ((n : ℝ) ^ 2 * t / 8) :=
    Real.one_le_exp (by positivity)
  have hX : (0 : ℝ) ≤ ρ ^ n / (2 * n) := by positivity
  nlinarith [hX, he]

/-- The same, in the `ENNReal.ofReal` form `hgbound` is stated in. -/
theorem hgbound_normalised {a₀ α W t K : ℝ} {n : ℕ}
    (hρ : 0 ≤ radiusOf a₀ α (Real.sqrt n / 2) t 0) (ht : 0 ≤ t)
    (h : ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (y ^ (n - 1) * profile a₀ α W n t y)
      ≤ ENNReal.ofReal ((radiusOf a₀ α (Real.sqrt n / 2) t 0) ^ n / (2 * n)
        + Real.exp (1 / 2) / ((n : ℝ) * α ^ n) * K * Real.exp ((n : ℝ) ^ 2 * t / 8))) :
    ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (y ^ (n - 1) * profile a₀ α W n t y)
      ≤ ENNReal.ofReal
        (((radiusOf a₀ α (Real.sqrt n / 2) t 0) ^ n / (2 * n)
          + Real.exp (1 / 2) / ((n : ℝ) * α ^ n) * K) * Real.exp ((n : ℝ) ^ 2 * t / 8)) :=
  le_trans h (ENNReal.ofReal_le_ofReal (const_normalise hρ ht))

/-! ## 2. `hpieces` at the chain's parameters

`pieces_sum_le` fed by `I1_le`, `I2_le`, `I3_le`, with the integrability from `ProfileBound6` and
`hJ` at `J = 3` from `HJ`.  The constant is

  `K = e⁶ + e³·(2/√(2π) + 2) + 2·e³`,

which is `hgbound_chained`'s `K` — the last free parameter in Lemma 4.3's constant. -/

theorem pieces_at_params {t A Y : ℝ} {n : ℕ} (hn : 0 < n) (ht : 0 ≤ t)
    (hts : Real.sqrt t ≤ 1 / 2) (hA1 : 1 ≤ A) (hAY : A ≤ Y)
    (hY : Y * Real.sqrt t ≤ 1 / 2)
    (hb2 : 2 ≤ (n : ℝ) * Real.sqrt t / 2)
    (hLb : (n : ℝ) * Real.sqrt t / 2 / 2 ≤ A)
    (hbA : (n : ℝ) * Real.sqrt t / 2 ≤ 2 * A)
    (hJ2 : ∀ y ∈ Ioc (1 : ℝ) A,
      y * Real.sqrt t + ((n : ℝ) + 2) / 2 * (y * Real.sqrt t) ^ 2 ≤ 3)
    (hJ3 : ∀ y ∈ Ioc A Y,
      y * Real.sqrt t + ((n : ℝ) + 2) / 2 * (y * Real.sqrt t) ^ 2 ≤ 3) :
    ((n : ℝ) * Real.sqrt t / 2) *
        ∫ y in Ioc (0 : ℝ) Y, Phi y * (1 - y * Real.sqrt t) ^ (-(((n : ℝ) + 2) / 2))
      ≤ (Real.exp 6 + Real.exp 3 * (2 / Real.sqrt (2 * π) + 2) + 2 * Real.exp 3)
        * Real.exp ((n : ℝ) ^ 2 * t / 8) := by
  have hs : (0 : ℝ) ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hAs : A * Real.sqrt t ≤ 1 / 2 :=
    le_trans (mul_le_mul_of_nonneg_right hAY hs) hY
  have hone : (0 : ℝ) ≤ 1 := zero_le_one
  -- the three pieces
  have b1 := I1_le (n := n) ht hn hts (integrableOn_pieces (n := n) le_rfl (by simpa using hts))
  have b2 := I2_le (n := n) (J := 3) ht hAs hb2 hLb hJ2
    (integrableOn_pieces (n := n) hone hAs) (integrableOn_rhs (n := n) (J := 3) le_rfl)
  have b3 := I3_le (n := n) (J := 3) ht hA1 hY hbA hJ3
    (integrableOn_pieces (n := n) (le_trans zero_le_one hA1) hY)
    (integrableOn_rhs (n := n) (J := 3) hA1)
  exact pieces_sum_le hA1 hAY hone
    (integrableOn_pieces (n := n) le_rfl (by simpa using hts))
    (integrableOn_pieces (n := n) hone hAs)
    (integrableOn_pieces (n := n) (le_trans zero_le_one hA1) hY)
    b1 b2 b3

end Submission.L10

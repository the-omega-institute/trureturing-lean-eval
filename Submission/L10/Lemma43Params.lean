/-
Gate L-10 (`klartag_packing`), brief 30, part 2.

**Lemma 4.3 at `Params`' fields.**  `hgbound_chained` (report 28) needs `windowRadius` to *be*
`radiusOf a₀ α (√n/2) t Y`, while `ChainDataInst.Params` only constrains it to be `< p`.  So the
instantiation needs a successor structure, `Params'`, which pins the window and the profile rather
than bounding them.

Two of `hgbound_chained`'s hypotheses are **derivable from `Params` alone** and are proved here:
`a₀ ≥ 1` and the gap `a₀ − 1/2 > 0`, both from `Params.a0_eq : a₀ = (1 − 1/n)⁻¹²`.
-/
import Submission.L10.HJ
import Submission.L10.ChainDataInst

namespace Submission.L10

open MeasureTheory Set Real Submission.L10.ChainDataInst
open scoped ENNReal NNReal

/-! ## 1. `a₀ ≥ 1` and the window gap, from `Params` alone -/

/-- `a₀ = (1 − 1/n)⁻¹² ≥ 1` for `n ≥ 2`.  `ha₀` of `hgbound_chained`. -/
theorem params_a0_ge_one {p n : ℕ} (P : Params p n) (hn : 2 ≤ n) : 1 ≤ P.a0 := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have h1 : (0 : ℝ) < 1 - 1 / (n : ℝ) := by
    have : 1 / (n : ℝ) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hn0 (by norm_num)]
      linarith
    linarith
  have h2 : 1 - 1 / (n : ℝ) ≤ 1 := by
    have : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
    linarith
  have hinv : (1 : ℝ) ≤ (1 - 1 / (n : ℝ))⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) h1]
    simp
  rw [P.a0_eq]
  nlinarith [hinv]

/-- The window gap `a₀ − 1/2 > 0`, which `integrableOn_shell_lhs` needs as its `ε`. -/
theorem params_a0_gap {p n : ℕ} (P : Params p n) (hn : 2 ≤ n) : 0 < P.a0 - 1 / 2 := by
  have := params_a0_ge_one P hn
  linarith

/-! ## 2. The successor structure

Everything `hgbound_chained` needs that `Params` does not already pin.  `Params'` extends `Params`
rather than replacing it, so `chainData_of_params` and `exists_good_line_of_params` still apply to
`toParams` unchanged. -/

/-- **`Params` with Lemma 4.3's window pinned.**  Six fields, and nothing else. -/
structure Params' (p n : ℕ) extends Params p n where
  /-- The `y`-window's right endpoint (Klartag's `C₀√n`). -/
  Y : ℝ
  Y_nonneg : 0 ≤ Y
  /-- `hgbound_chained`'s `hWdef`: the window radius is *defined* by the substitution, not bounded. -/
  windowRadius_eq : windowRadius = radiusOf a0 alpha (Real.sqrt n / 2) T Y
  /-- `hwin`: one inequality implying the whole window group (report 27 §4). -/
  window_small : Y * Real.sqrt T ≤ 1 / 2
  /-- `n₁` of `HJ.junk_endpoint_le_three`.  The true threshold is 839; this is the cheaply
  provable one (report 30 §1). -/
  n_large : 2073600 ≤ n
  /-- Lemma 4.3's profile is `Profile.profile` at these parameters. -/
  f_eq : f = profile a0 alpha windowRadius n T

/-- `Params'` inherits `a₀ ≥ 1`. -/
theorem Params'.a0_ge_one {p n : ℕ} (P : Params' p n) : 1 ≤ P.a0 :=
  params_a0_ge_one P.toParams (by have := P.n_large; omega)

theorem Params'.a0_gap {p n : ℕ} (P : Params' p n) : 0 < P.a0 - 1 / 2 :=
  params_a0_gap P.toParams (by have := P.n_large; omega)

theorem Params'.dim_pos' {p n : ℕ} (P : Params' p n) : 0 < n := by
  have := P.n_large; omega

/-- The window group, discharged for `Params'` (report 27 §4). -/
theorem Params'.window_sub_pos {p n : ℕ} (P : Params' p n) {y : ℝ} (hyY : y ≤ P.Y) :
    0 < P.a0 - Real.sqrt P.T * y :=
  _root_.Submission.L10.window_sub_pos P.a0_ge_one hyY P.window_small

theorem Params'.window_one_sub_pos {p n : ℕ} (P : Params' p n) {y : ℝ} (hyY : y ≤ P.Y) :
    0 < 1 - Real.sqrt P.T * y :=
  _root_.Submission.L10.window_one_sub_pos hyY P.window_small

/-- `hgbound_chained`'s `hWY`, `hρ`, `hρW`, from monotonicity of `radiusOf`. -/
theorem Params'.radius_le {p n : ℕ} (P : Params' p n) (hT : 0 < P.T) {y : ℝ}
    (hy0 : 0 ≤ y) (hyY : y ≤ P.Y) :
    radiusOf P.a0 P.alpha (Real.sqrt n / 2) P.T y ≤ P.windowRadius := by
  rw [P.windowRadius_eq]
  exact radiusOf_le_end P.alpha_pos hT P.Y_nonneg hy0 hyY
    (fun z hz => P.window_sub_pos hz.2)

theorem Params'.radius_nonneg {p n : ℕ} (P : Params' p n) :
    0 ≤ radiusOf P.a0 P.alpha (Real.sqrt n / 2) P.T 0 :=
  radiusOf_nonneg P.alpha_pos (by positivity) (lt_of_lt_of_le zero_lt_one P.a0_ge_one)

end Submission.L10

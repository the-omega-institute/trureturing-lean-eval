import Submission.L10.ChainInputDom
import Submission.L10.WindowR

/-!
# Gate L-10 (`klartag_packing`), brief 72 — `ChainInputDom` at the reach window

Report 68 §1 showed the far band is genuinely reachable, so the window must move out from
`windowC` to `WindowR.windowR`.  This module is `ChainInputDom`'s one `windowC`-naming
declaration, copied with `windowC α n → windowR α n`.  Everything else in `ChainInputDom`
(`profileAt`, `profileAt_antitone`, `dom_of_tail`, `profileAt_eq_Phi`, …) is general in the window
and is **called**, not copied.
-/

set_option linter.unusedSectionVars false

namespace Submission.L10

open MeasureTheory Set Real Submission.L10.ChainDataInst Submission.L10.Tiling
open Submission.L10.Section5 Submission.L10.ConstructionA Submission.L10.WindowR
open scoped ENNReal NNReal

structure ChainRawR (p n : ℕ) where
  alpha : ℝ
  alpha_pos : 0 < alpha
  alpha_norm : alpha ^ n * ((p ^ (n - 1) : ℕ) : ℝ) = kappa n
  R : ℝ
  R_nonneg : 0 ≤ R
  R_scaled : alpha * R ≤ 1 - 1 / (n : ℝ)
  R_lt_p : R < (p : ℝ)
  tiling_defect : (n : ℝ) * (alpha * Real.sqrt n / 2) ≤ 1 / 4
  window_lt_p : windowR alpha n < (p : ℝ)
  w : (Fin n → ℤ) → ℝ≥0∞
  supp : Finset (Fin n → ℤ)
  supp_ne_zero : ∀ y ∈ supp, y ≠ 0
  supp_radius : ∀ y ∈ supp, ‖toE n y‖ ≤ windowR alpha n
  /-- **The only probabilistic input.**  Proposition 4.1 at each horizon `t`, at the lattice
  point's own radius. -/
  tail : ∀ y ∈ supp, w y ≤ ENNReal.ofReal
    (∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
      profileAt (a0C n) alpha (windowR alpha n) n t ‖toE n y‖)
  arith : (n : ℝ) * kappa n * ((p : ℝ) - 1) * (8 - 8 / (n : ℝ) ^ 2) < 8 * ((p : ℝ) ^ n - 1)

end Submission.L10

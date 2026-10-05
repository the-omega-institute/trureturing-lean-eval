/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/

import Mathlib.Probability.Distributions.SetBernoulli
import Submission.Thresholds
import LeanPool.KahnKalai
import ChallengeDeps
/-!
# Main Statement from Thresholds versus fractional expectation-thresholds

We formalise the statement of the main result from K. Frankston, J. Kahn, B. Narayanan, and J. Park,
`Thresholds versus fractional expectation-thresholds`, Annals of Math, 194 (2) 2021.
-/


namespace Submission

open _root_.FractionalExpectationThresholds
set_option autoImplicit false

namespace FractionalExpectationThresholds

open ProbabilityTheory unitInterval Set

open scoped NNReal

section Definitions









end Definitions

/-- The constant `K` in Theorem 1.1. -/
-- Park–Pham proof from lean-pool `LeanPool/KahnKalai` (Apache-2.0).
noncomputable def K : ℝ := KahnKalai.parkPhamK / Real.log 2

/--
Statement of Theorem 1.1:

There exists a universal constant `K` such that for any finite set `X` and any increasing
collection of sets `𝓕` such that `l(𝓕)` is at least `2`,

`p_c(𝓕) ≤ K * q_f(𝓕) * log l(𝓕)`.

Note: The assumption that `l(𝓕)` is at least `2` is not explicitly in the paper but is needed
because if `l(𝓕) = 1` then `Real.log (l 𝓕) = 0`, but `p_c 𝓕 ∈ (0,1)` (so the inequality clearly
cannot hold).
-/
theorem theorem_1_1 (X : Type*) [Fintype X] (𝓕 : Set (Set X)) (h𝓕 : IsUpperSet 𝓕)
    (hl𝓕 : 2 ≤ l 𝓕) : p_c 𝓕 ≤ K * q_f 𝓕 * Real.log (l 𝓕) := by
  classical
  let e := Fintype.equivFin X
  let F := KahnKalai.minimals (Submission.Helpers.family e 𝓕)
  have hK : 0 ≤ K := div_nonneg KahnKalai.parkPhamK_pos.le (Real.log_pos (by norm_num)).le
  have hlog : 0 ≤ Real.log (l 𝓕) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ l 𝓕 from (by omega)))
  calc
    (p_c 𝓕 : ℝ) ≤ KahnKalai.threshold F :=
      Submission.Helpers.chosen_threshold_le e 𝓕 h𝓕
    _ ≤ KahnKalai.parkPhamK * KahnKalai.expectationThreshold F * Real.logb 2 (l 𝓕) :=
      KahnKalai.park_pham_bound F (l 𝓕) hl𝓕 (Submission.Helpers.minimals_bounded e 𝓕)
    _ = K * KahnKalai.expectationThreshold F * Real.log (l 𝓕) := by
      rw [K, Real.logb]
      ring
    _ ≤ K * q_f 𝓕 * Real.log (l 𝓕) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Submission.Helpers.integral_threshold_le_fractional e 𝓕) hK)
        hlog

end FractionalExpectationThresholds

end Submission

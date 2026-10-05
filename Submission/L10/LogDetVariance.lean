import Submission.L10.DriftAccumulated

/-!
# Gate L-10 (`klartag_packing`), brief 94a — the one-step log-determinant **lower** bound

Report 93 §9: the existence step is Markov against the crude floor `L = n·log(mAt n c₃)`
(`GoodPathBounds.stoppedLogDet_ge`), so its margin is `≈ C'/(C' + n|log m|)` and decays like `1/n`,
while the count failure decays like `n^{−3/4}`.  Brief 94's fix replaces the floor by a
second-moment bound on the stopped log-determinant, and the first thing that needs is a **lower**
one-step bound: the tree has only upper ones.

`Submission.L10.log_det_add_le` / `log_det_add_le_kappa` (`OneStep.lean:206`, `:242`) and
`StepInputs2.log_det_step_unconj` (`:717`) are all of the form
`log det (A + H) ≤ log det A + tr(A⁻¹H) − (quadratic gain)`, and there is **no two-sided form**:
report 88 got `liftCost_nonneg` by running the *upper* bound backwards, at the lifted state with
`H = −Δ`, which gives a lower bound on `log det A` in terms of `log det (A+Δ)` — not what a
variance bound needs, since there the base point must stay `A_k`.

## What is here

* `log_one_add_ge` — the scalar hinge: `log(1+x) ≥ x − 2x²` for `x ≥ −1/2`.  One `nlinarith` on
  `x²(1 + 2x) ≥ 0` from `Real.one_sub_inv_le_log_of_pos`.  The constant `2` (rather than `1`, which
  is also true) is what makes the proof one line from Mathlib's bound.
* `log_det_one_add_ge` — the spectral form, `tr B − 2‖B‖_F² ≤ log det (1 + B)` whenever every
  eigenvalue of the Hermitian `B` is `≥ −1/2`.  Mirrors `OneStep.log_det_one_add_le`.
* `log_det_add_ge` — the cone form, mirroring `OneStep.log_det_add_le`:
  `log det A + tr(A⁻¹H) − 2‖SHS‖_F² ≤ log det (A + H)`.
* `log_det_add_ge_of_stateBounds` — the form the chain uses:
  `log det A + tr(A⁻¹H) − (2/m²)‖H‖_F² ≤ log det (A + H)` on `Discharge.StateBounds A m M`, with
  the single side condition `‖H‖_op ≤ m/2`.

Together with the frozen upper bounds this is the two-sided one-step inequality brief 94a item (1)
asks for; §5 records exactly what items (2)–(4) still need.

Nothing reported is edited.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Submission.L10.LogDetVariance

open MeasureTheory Matrix Finset Module
open scoped RealInnerProductSpace
open Submission.L10 Submission.L10.Increments

/-! ## 1. The scalar hinge -/

/-- **`log(1+x) ≥ x − 2x²` for `x ≥ −1/2`.**  From `1 − (1+x)⁻¹ ≤ log(1+x)`: the gap is
`x²(1+2x)/(1+x) ≥ 0`.  At `x = −1/2` it reads `−0.693 ≥ −1`. -/
theorem log_one_add_ge {x : ℝ} (hx : -(1 / 2 : ℝ) ≤ x) :
    x - 2 * x ^ 2 ≤ Real.log (1 + x) := by
  have h1 : (0 : ℝ) < 1 + x := by linarith
  have h2 : 1 - (1 + x)⁻¹ ≤ Real.log (1 + x) := Real.one_sub_inv_le_log_of_pos h1
  have hkey : (x - 2 * x ^ 2) * (1 + x) ≤ x := by
    nlinarith [mul_nonneg (sq_nonneg x) (by linarith : (0 : ℝ) ≤ 1 + 2 * x)]
  have h3 : x - 2 * x ^ 2 ≤ 1 - (1 + x)⁻¹ := by
    have heq : 1 - (1 + x)⁻¹ = x / (1 + x) := by
      field_simp
      ring
    rw [heq, le_div_iff₀ h1]
    exact hkey
  linarith

/-! ## 2. The spectral form -/

section Spectral

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **`OneStep.log_det_one_add_le`, downward.**  If every eigenvalue of the Hermitian `B` is at
least `−1/2` then `tr B − 2‖B‖_F² ≤ log det (1 + B)`. -/
theorem log_det_one_add_ge {B : Matrix n n ℝ} (hB : B.IsHermitian)
    (hlow : ∀ i, -(1 / 2 : ℝ) ≤ hB.eigenvalues i) :
    B.trace - 2 * (∑ i, (hB.eigenvalues i) ^ 2) ≤ Real.log (1 + B).det := by
  have hpos : ∀ i, (0 : ℝ) < 1 + hB.eigenvalues i := fun i => by linarith [hlow i]
  rw [Submission.L10.det_one_add_eq_prod hB,
    Real.log_prod (fun i _ => ne_of_gt (hpos i)),
    Submission.L10.trace_eq_sum_eigenvalues_real hB, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun i _ => log_one_add_ge (hlow i)

end Spectral

/-! ## 3. The cone form -/

section Cone

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The one-step log-determinant inequality, lower direction.**  `S` is any symmetric congruence
factor with `S A S = 1`; the hypothesis is that `B = S H S` has no eigenvalue below `−1/2`, i.e.
that the step does not halve the state in any direction. -/
theorem log_det_add_ge {A H S : Matrix n n ℝ} (hA : A.PosDef)
    (hS : S.IsHermitian) (hSA : S * A * S = 1) (hH : H.IsHermitian)
    (hlow : ∀ i, -(1 / 2 : ℝ) ≤ (Submission.L10.IsHermitian.conj' hS hH).eigenvalues i) :
    Real.log A.det + (A⁻¹ * H).trace - 2 * (∑ i, ∑ j, ((S * H * S) i j) ^ 2)
      ≤ Real.log (A + H).det := by
  have hB := Submission.L10.IsHermitian.conj' hS hH
  have hpos : ∀ i, (0 : ℝ) < 1 + hB.eigenvalues i := fun i => by linarith [hlow i]
  have hSS : S * S * A = 1 := by
    have h1 : (S * A) * S = 1 := hSA
    have h2 : S * (S * A) = 1 := _root_.mul_eq_one_comm.mp h1
    rw [← mul_assoc] at h2
    exact h2
  have hAinv : A⁻¹ = S * S := Matrix.inv_eq_left_inv hSS
  have hcong : S * (A + H) * S = 1 + S * H * S := by
    rw [Matrix.mul_add, Matrix.add_mul, hSA]
  have hdetA : 0 < A.det := hA.det_pos
  have hdetS : S.det * A.det * S.det = 1 := by
    have h := congrArg Matrix.det hSA
    rwa [Matrix.det_mul, Matrix.det_mul, Matrix.det_one] at h
  have hcongdet : S.det * (A + H).det * S.det = (1 + S * H * S).det := by
    have h := congrArg Matrix.det hcong
    rwa [Matrix.det_mul, Matrix.det_mul] at h
  have hdet : (A + H).det = A.det * (1 + S * H * S).det := by
    linear_combination A.det * hcongdet - (A + H).det * hdetS
  have htr : (A⁻¹ * H).trace = (S * H * S).trace := by
    rw [hAinv, Matrix.trace_mul_cycle S H S]
  have hposdet : 0 < (1 + S * H * S).det := by
    rw [Submission.L10.det_one_add_eq_prod hB]
    exact Finset.prod_pos fun i _ => hpos i
  rw [hdet, Real.log_mul (ne_of_gt hdetA) (ne_of_gt hposdet), htr,
    ← Submission.L10.sum_sq_eigenvalues_eq_frobenius hB]
  linarith [log_det_one_add_ge hB hlow]

end Cone

/-! ## 4. The form the chain uses -/

section Chain

variable {n : ℕ}

/-- `‖A⁻¹‖_op ≤ 1/m` from the state bounds. -/
theorem opNorm_inv_le {A : Matrix (Fin n) (Fin n) ℝ} {m M : ℝ}
    (hSB : Discharge.StateBounds A m M) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹‖ ≤ 1 / m := by
  have hm := hSB.mpos
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
  have h := DriftStopped2.norm_inv_apply_le hSB y
  rw [div_eq_inv_mul] at h
  calc ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ y‖ ≤ m⁻¹ * ‖y‖ := h
    _ = 1 / m * ‖y‖ := by rw [one_div]

/-- **The lower one-step bound on the state bounds.**  The only side condition is
`‖H‖_op ≤ m/2`: it makes every eigenvalue of `S H S` at least `−1/2`, since
`‖S‖_op² ≤ ‖A⁻¹‖_op ≤ 1/m`. -/
theorem log_det_add_ge_of_stateBounds {A H : Matrix (Fin n) (Fin n) ℝ} {m M : ℝ}
    (hSB : Discharge.StateBounds A m M) (hH : H.IsHermitian)
    (hop : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) H‖ ≤ m / 2) :
    Real.log A.det + (A⁻¹ * H).trace - (2 / m ^ 2) * (∑ i, ∑ j, (H i j) ^ 2)
      ≤ Real.log (A + H).det := by
  classical
  obtain ⟨S, hSherm, hSA⟩ := hSB.congr
  have hm := hSB.mpos
  have hSsym : S.IsSymm := Matrix.isHermitian_iff_isSymm.1 hSherm
  have hSS : S * S * A = 1 := by
    have h1 : (S * A) * S = 1 := hSA
    have h2 : S * (S * A) = 1 := _root_.mul_eq_one_comm.mp h1
    rw [← mul_assoc] at h2
    exact h2
  have hAinv : A⁻¹ = S * S := Matrix.inv_eq_left_inv hSS
  -- `‖S‖² ≤ 1/m`
  have hS2 : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S‖ ^ 2 ≤ 1 / m := by
    refine le_trans (StepInputs2.opNorm_sq_le_of_sq (A := A⁻¹) hSsym ?_) (opNorm_inv_le hSB)
    exact hAinv.symm
  have hS0 : (0 : ℝ) ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S‖ := norm_nonneg _
  have hH0 : (0 : ℝ) ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) H‖ := norm_nonneg _
  -- the Frobenius bound on the conjugate
  have hfrob : ∑ i, ∑ j, ((S * H * S) i j) ^ 2
      ≤ (1 / m ^ 2) * ∑ i, ∑ j, (H i j) ^ 2 := by
    have h1 : ∑ i, ∑ j, ((S * H * S) i j) ^ 2
        ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S‖ ^ 2 * ∑ i, ∑ j, ((S * H) i j) ^ 2 :=
      StepInputs2.frobenius_mul_right_le (S * H) S hSsym
    have h2 : ∑ i, ∑ j, ((S * H) i j) ^ 2
        ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S‖ ^ 2 * ∑ i, ∑ j, (H i j) ^ 2 :=
      StepInputs2.frobenius_mul_left_le S H
    have hHF0 : (0 : ℝ) ≤ ∑ i, ∑ j, (H i j) ^ 2 := by positivity
    have hS20 : (0 : ℝ) ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S‖ ^ 2 := by positivity
    have h3 : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S‖ ^ 2 * ∑ i, ∑ j, ((S * H) i j) ^ 2
        ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S‖ ^ 2
          * (‖Matrix.toEuclideanCLM (𝕜 := ℝ) S‖ ^ 2 * ∑ i, ∑ j, (H i j) ^ 2) :=
      mul_le_mul_of_nonneg_left h2 hS20
    have h4 : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S‖ ^ 2
          * (‖Matrix.toEuclideanCLM (𝕜 := ℝ) S‖ ^ 2 * ∑ i, ∑ j, (H i j) ^ 2)
        ≤ (1 / m) * ((1 / m) * ∑ i, ∑ j, (H i j) ^ 2) := by
      have hstep : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S‖ ^ 2 * ∑ i, ∑ j, (H i j) ^ 2
          ≤ (1 / m) * ∑ i, ∑ j, (H i j) ^ 2 :=
        mul_le_mul_of_nonneg_right hS2 hHF0
      have hrhs0 : (0 : ℝ) ≤ (1 / m) * ∑ i, ∑ j, (H i j) ^ 2 := by positivity
      nlinarith [hS2, hS20, hstep, hHF0]
    have h5 : (1 / m) * ((1 / m) * ∑ i, ∑ j, (H i j) ^ 2)
        = (1 / m ^ 2) * ∑ i, ∑ j, (H i j) ^ 2 := by
      field_simp
    linarith
  -- the eigenvalue side condition
  have hopSHS : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (S * H * S)‖ ≤ 1 / 2 := by
    have hmul : Matrix.toEuclideanCLM (𝕜 := ℝ) (S * H * S)
        = Matrix.toEuclideanCLM (𝕜 := ℝ) S * Matrix.toEuclideanCLM (𝕜 := ℝ) H
          * Matrix.toEuclideanCLM (𝕜 := ℝ) S := by
      rw [map_mul, map_mul]
    rw [hmul]
    have hb1 : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S * Matrix.toEuclideanCLM (𝕜 := ℝ) H
          * Matrix.toEuclideanCLM (𝕜 := ℝ) S‖
        ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) H‖
          * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S‖ :=
      le_trans (norm_mul_le _ _) (mul_le_mul_of_nonneg_right (norm_mul_le _ _) hS0)
    have hb2 : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) H‖
          * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S‖
        = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S‖ ^ 2 * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) H‖ := by
      ring
    rw [hb2] at hb1
    have hb3 : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S‖ ^ 2 * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) H‖
        ≤ (1 / m) * (m / 2) := by
      have := mul_le_mul hS2 hop hH0 (by positivity)
      exact this
    have hb4 : (1 / m) * (m / 2) = 1 / 2 := by field_simp
    linarith
  have hlow : ∀ i, -(1 / 2 : ℝ)
      ≤ (Submission.L10.IsHermitian.conj' hSherm hH).eigenvalues i := by
    intro i
    have habs := GoodEvent.abs_eigenvalues_le_opNorm
      (Submission.L10.IsHermitian.conj' hSherm hH) i
    have := abs_le.1 (le_trans habs hopSHS)
    linarith [this.1]
  have hmain := log_det_add_ge hSB.posDef hSherm hSA hH hlow
  have hid : (2 / m ^ 2) * (∑ i, ∑ j, (H i j) ^ 2)
      = 2 * ((1 / m ^ 2) * ∑ i, ∑ j, (H i j) ^ 2) := by ring
  rw [hid]
  linarith [hmain, hfrob]

end Chain

/-! ## 5. The martingale increment's conditional second moment -/

section Increment

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **`E[⟪V, ξ⟫² | ℱ] = v · ‖V‖²`** for an `ℱ`-measurable coefficient `V` and an increment with
isotropic covariance `v`.  This is `StepInputs2.condExp_quadForm` at `M = V ⊗ V`, and it is the
second half of brief 94a item (2): the first half, `E[⟪V, ξ⟫ | ℱ] = 0`, is
`StepInputs2.condExp_inner_eq_zero` unchanged.

At the chain, `V = π_k (matToUT A_k⁻¹)` and `v = h`, so `DriftStopped2.norm_stoppedV_le`'s
`‖V‖ ≤ √n / m` turns this into the per-step bound `h · n / m²`. -/
theorem condExp_inner_sq {V ξ : Ω → EuclideanSpace ℝ ι} {v : ℝ}
    (hξm : Measurable[mΩ] ξ)
    (hcov : ∀ p q : ι, ∫ ω, ξ ω p * ξ ω q ∂P = if p = q then v else 0)
    (hintprod : ∀ p q : ι, Integrable (fun ω => ξ ω p * ξ ω q) P)
    (hint : ∀ p q : ι, Integrable (fun ω => (V ω p * V ω q) * (ξ ω p * ξ ω q)) P)
    {ℱ : MeasurableSpace Ω} (hℱ : ℱ ≤ mΩ) [SigmaFinite (P.trim hℱ)]
    (hV : ∀ p, StronglyMeasurable[ℱ] fun ω => V ω p)
    (hind : ProbabilityTheory.Indep (MeasurableSpace.comap ξ inferInstance) ℱ P) :
    P[fun ω => (⟪V ω, ξ ω⟫ : ℝ) ^ 2 | ℱ] =ᵐ[P] fun ω => v * ‖V ω‖ ^ 2 := by
  classical
  letI : MeasurableSpace Ω := mΩ
  have hrw : (fun ω => (⟪V ω, ξ ω⟫ : ℝ) ^ 2)
      = fun ω => ∑ p, ∑ q, (V ω p * V ω q) * (ξ ω p * ξ ω q) := by
    funext ω
    have hin : (⟪V ω, ξ ω⟫ : ℝ) = ∑ p, V ω p * ξ ω p := by
      simp [PiLp.inner_apply, mul_comm]
    rw [hin, sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
  rw [hrw]
  refine (StepInputs2.condExp_quadForm (M := fun ω p q => V ω p * V ω q) hℱ
    (fun p q => ((hV p).mul (hV q) :
      StronglyMeasurable[ℱ] fun ω => V ω p * V ω q)) hξm hind hcov hintprod hint).trans ?_
  refine Filter.Eventually.of_forall fun ω => ?_
  have hnorm : ‖V ω‖ ^ 2 = ∑ p, V ω p * V ω p := by
    rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
    simp [sq]
  simp only [hnorm]

end Increment

/-! ## 6. The variance bound, named -/

section Var

/-- **The announced variance bound** `Var(M_N) ≤ T · n / m²`.  `N` steps, each contributing
`h · ‖V_k‖² ≤ h · n / m²` (§5 with `DriftStopped2.norm_stoppedV_le`), and `N · h = T` exactly
(`ParamsAdopted2.numStepsAdopted2_mul_stepSizeAdopted2`). -/
noncomputable def varBound (n : ℕ) (c₃ : ℝ) : ℝ :=
  ChainDrift.horizon n * (n : ℝ) / GoodPathBounds.mAt n c₃ ^ 2

/-- `varBound ≤ 64 · log n / n` at any admissible contact threshold — the state's lower bound is
at least `1/2` (`GoodPathBounds.half_le_mAt`), and `T = 16 log n / n²`. -/
theorem varBound_le {n : ℕ} (hn : 2073600 ≤ n) {c₃ : ℝ}
    (hc₃ : c₃ * DriftStopped6.etaAdopted n ≤ 1 / 4) :
    varBound n c₃ ≤ 64 * Real.log n / (n : ℝ) := by
  have hnR : (2073600 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hm := GoodPathBounds.half_le_mAt hn hc₃
  have hm0 : (0 : ℝ) < GoodPathBounds.mAt n c₃ := by linarith
  have hlog : (0 : ℝ) ≤ Real.log n := by
    have h3 : 3 ≤ n := by omega
    exact le_trans (by norm_num) (ChainDrift.log_pos_of_three h3)
  have hsq : (1 : ℝ) / 4 ≤ GoodPathBounds.mAt n c₃ ^ 2 := by nlinarith
  rw [varBound, div_le_div_iff₀ (by positivity) hn0]
  have hTn : ChainDrift.horizon n * (n : ℝ) * (n : ℝ) = 16 * Real.log n := by
    rw [ChainDrift.horizon]
    field_simp
  rw [hTn]
  nlinarith [hsq, hlog]

end Var

end Submission.L10.LogDetVariance

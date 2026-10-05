/-
Gate L-10 (`klartag_packing`), brief 2.

The **one-step log-det inequality on the positive-definite cone** — the discrete replacement for
Itô's formula applied to `F(X) = log det X` (Klartag, arXiv:2504.05042, Lemma 3.3, p. 14-15,
together with the local-martingale-is-a-martingale step used there).

The continuous proof expands `log det(P + εB)` to second order and integrates the Itô drift
`-(1/2)∫ δ_s ds`.  Here that is replaced by a *finite, exact* inequality: for a positive definite
`A` and a symmetric `H`,

  `log det (A + H) ≤ log det A + tr (A⁻¹ H) − ‖A^{-1/2} H A^{-1/2}‖_F² / (2 M)`

where `M` is any upper bound (`≥ 1`) for the eigenvalues of `A^{-1/2}(A+H)A^{-1/2}`.  Summing this
along the steps of the discrete chain *is* the Riemann sum, so no limit is taken and no
integrability argument is needed.

Following rule 7 (generic over pinned) the square root is **not** a definition here: the statement
takes any symmetric `S` with `S * A * S = 1` as the congruence factor, so a caller may instantiate
`S := CFC.sqrt A⁻¹` or anything else.
-/
import Mathlib

namespace Submission.L10

open Real Finset Matrix

/-! ## 1. The scalar inequality

`log v ≤ (v − 1) − (v − 1)²/(2M)` for `0 < v ≤ M`, `1 ≤ M`.  This is the whole analytic content:
the second-order term is what produces the drift `−Tr[π]/(2‖A‖²_op)` of Lemma 3.3.
-/

/-- **The scalar one-step inequality.**  For `1 ≤ M` and `0 < v ≤ M`,
`log v ≤ (v − 1) − (v − 1)² / (2 M)`.

`M` is sharp: `g v = (v−1) − (v−1)²/(2M) − log v` has `g' v = (v−1)(M−v)/(vM)`, which changes
sign at `v = M`. -/
theorem log_le_sub_one_sub_sq {M v : ℝ} (hM : 1 ≤ M) (hv : 0 < v) (hvM : v ≤ M) :
    Real.log v ≤ (v - 1) - (v - 1) ^ 2 / (2 * M) := by
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM
  set f : ℝ → ℝ := fun x => (x - 1) - (x - 1) ^ 2 / (2 * M) - Real.log x with hfdef
  set g : ℝ → ℝ := fun x => (x - 1) * (M - x) / (x * M) with hgdef
  have hderiv : ∀ x : ℝ, x ≠ 0 → HasDerivAt f (g x) x := by
    intro x hx
    have hA : HasDerivAt (fun y : ℝ => y - 1) 1 x := (hasDerivAt_id x).sub_const 1
    have hsq : HasDerivAt (fun y : ℝ => (y - 1) ^ 2) (2 * (x - 1)) x := by
      have h := (hasDerivAt_pow 2 (x - 1)).comp x hA
      simpa [Function.comp_def] using h
    have hC : HasDerivAt (fun y : ℝ => (y - 1) ^ 2 / (2 * M)) (2 * (x - 1) / (2 * M)) x :=
      hsq.div_const _
    have hD : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx
    have h1 : HasDerivAt f (1 - 2 * (x - 1) / (2 * M) - x⁻¹) x := (hA.sub hC).sub hD
    have heq : 1 - 2 * (x - 1) / (2 * M) - x⁻¹ = g x := by
      rw [hgdef]; field_simp; ring
    rwa [heq] at h1
  have hcont : ContinuousOn f {(0 : ℝ)}ᶜ := by
    refine ContinuousOn.sub ?_ Real.continuousOn_log
    exact Continuous.continuousOn (by fun_prop)
  have hf1 : f 1 = 0 := by simp [hfdef]
  have key : 0 ≤ f v := by
    rcases le_total v 1 with hv1 | hv1
    · have hsub : Set.Icc v 1 ⊆ {(0 : ℝ)}ᶜ := fun x hx => ne_of_gt (lt_of_lt_of_le hv hx.1)
      have hanti : AntitoneOn f (Set.Icc v 1) := by
        apply antitoneOn_of_hasDerivWithinAt_nonpos (f' := g) (convex_Icc v 1) (hcont.mono hsub)
        · intro x hx
          rw [interior_Icc] at hx
          exact (hderiv x (ne_of_gt (lt_of_lt_of_le hv hx.1.le))).hasDerivWithinAt
        · intro x hx
          rw [interior_Icc] at hx
          have hx0 : 0 < x := lt_of_lt_of_le hv hx.1.le
          rw [hgdef]
          refine div_nonpos_iff.2 (Or.inr ⟨?_, ?_⟩)
          · refine mul_nonpos_iff.2 (Or.inr ⟨by linarith [hx.2], by linarith [hx.2]⟩)
          · positivity
      have hle := hanti (Set.left_mem_Icc.2 hv1) (Set.right_mem_Icc.2 hv1) hv1
      linarith [hle, hf1.ge, hf1.le]
    · have hsub : Set.Icc (1 : ℝ) M ⊆ {(0 : ℝ)}ᶜ :=
        fun x hx => ne_of_gt (lt_of_lt_of_le zero_lt_one hx.1)
      have hmono : MonotoneOn f (Set.Icc (1 : ℝ) M) := by
        apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := g) (convex_Icc 1 M) (hcont.mono hsub)
        · intro x hx
          rw [interior_Icc] at hx
          exact (hderiv x (ne_of_gt (lt_trans zero_lt_one hx.1))).hasDerivWithinAt
        · intro x hx
          rw [interior_Icc] at hx
          have hx0 : 0 < x := lt_trans zero_lt_one hx.1
          rw [hgdef]
          refine div_nonneg (mul_nonneg (by linarith [hx.1]) (by linarith [hx.2])) (by positivity)
      have hle := hmono (Set.left_mem_Icc.2 hM) (Set.mem_Icc.2 ⟨hv1, hvM⟩) hv1
      linarith [hle, hf1.ge, hf1.le]
  have hsplit : Real.log v = (v - 1) - (v - 1) ^ 2 / (2 * M) - f v := by rw [hfdef]; ring
  rw [hsplit]; linarith

/-- The form used in the paper: `log (1 + u) ≤ u − u²/(2κ²)` whenever `1 ≤ κ`, `−1 < u` and
`1 + u ≤ κ`.  (`κ` is `λ_max(A+H)/λ_min(A) ⊔ 1`.) -/
theorem log_one_add_le_sub_sq {κ u : ℝ} (hκ : 1 ≤ κ) (hu : -1 < u) (huκ : 1 + u ≤ κ) :
    Real.log (1 + u) ≤ u - u ^ 2 / (2 * κ ^ 2) := by
  have hκ2 : (1 : ℝ) ≤ κ ^ 2 := by nlinarith
  have h := log_le_sub_one_sub_sq hκ2 (by linarith : (0 : ℝ) < 1 + u)
    (by nlinarith : 1 + u ≤ κ ^ 2)
  simpa using h

/-! ## 2. From the eigenvalues to `det` and `trace` -/

section Spectral

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `trace` of a real Hermitian matrix, with the `RCLike.ofReal` coercion discharged. -/
theorem trace_eq_sum_eigenvalues_real {B : Matrix n n ℝ} (hB : B.IsHermitian) :
    B.trace = ∑ i, hB.eigenvalues i := by
  simpa using hB.trace_eq_sum_eigenvalues

/-- The spectral decomposition of a real Hermitian matrix, coercion discharged. -/
theorem spectral_real {B : Matrix n n ℝ} (hB : B.IsHermitian) :
    B = (hB.eigenvectorUnitary : Matrix n n ℝ) * Matrix.diagonal hB.eigenvalues *
      star (hB.eigenvectorUnitary : Matrix n n ℝ) := by
  have hco : (RCLike.ofReal ∘ hB.eigenvalues : n → ℝ) = hB.eigenvalues := by
    funext i; simp
  conv_lhs => rw [hB.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply, hco]

/-- `det (1 + B) = ∏ (1 + λᵢ)` for Hermitian `B`. -/
theorem det_one_add_eq_prod {B : Matrix n n ℝ} (hB : B.IsHermitian) :
    (1 + B).det = ∏ i, (1 + hB.eigenvalues i) := by
  set U : Matrix n n ℝ := (hB.eigenvectorUnitary : Matrix n n ℝ) with hU
  set D : Matrix n n ℝ := Matrix.diagonal hB.eigenvalues with hD
  have hUstar : U * star U = 1 := hB.eigenvectorUnitary.2.2
  have hB' : B = U * D * star U := by rw [hU, hD]; exact spectral_real hB
  have hdec : (1 : Matrix n n ℝ) + B = U * (1 + D) * star U := by
    rw [mul_add, add_mul, mul_one, hUstar, ← hB']
  have hdet : (U * (1 + D) * star U).det = (1 + D).det := by
    rw [Matrix.det_mul, Matrix.det_mul, mul_comm U.det, mul_assoc, ← Matrix.det_mul, hUstar,
      Matrix.det_one, mul_one]
  have hdiag : (1 : Matrix n n ℝ) + D = Matrix.diagonal (fun i => 1 + hB.eigenvalues i) := by
    rw [hD, ← Matrix.diagonal_one, Matrix.diagonal_add]
  rw [hdec, hdet, hdiag, Matrix.det_diagonal]

/-- `tr (B * B) = Σ λᵢ²` for Hermitian `B`. -/
theorem trace_mul_self_eq_sum_sq {B : Matrix n n ℝ} (hB : B.IsHermitian) :
    (B * B).trace = ∑ i, (hB.eigenvalues i) ^ 2 := by
  set U : Matrix n n ℝ := (hB.eigenvectorUnitary : Matrix n n ℝ) with hU
  set D : Matrix n n ℝ := Matrix.diagonal hB.eigenvalues with hD
  have hUs : star U * U = 1 := hB.eigenvectorUnitary.2.1
  have hB' : B = U * D * star U := by rw [hU, hD]; exact spectral_real hB
  have hBB : B * B = U * (D * D) * star U := by
    conv_lhs => rw [hB']
    simp only [mul_assoc]
    rw [← mul_assoc (star U) U (D * star U), hUs, one_mul]
  rw [hBB, Matrix.trace_mul_cycle, ← mul_assoc, hUs, one_mul, hD,
    Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  exact Finset.sum_congr rfl (fun i _ => (sq _).symm)

omit [DecidableEq n] in
/-- `tr (B * B) = Σᵢⱼ Bᵢⱼ²` for Hermitian `B`: the Frobenius norm squared, entrywise. -/
theorem trace_mul_self_eq_sum_sq_entries [DecidableEq n] {B : Matrix n n ℝ} (hB : B.IsHermitian) :
    (B * B).trace = ∑ i, ∑ j, (B i j) ^ 2 := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  have hsym : B j i = B i j := by
    have h2 : Bᴴ i j = B i j := by rw [hB]
    simpa [Matrix.conjTranspose_apply] using h2
  rw [hsym, sq]

/-- The Frobenius norm squared of a Hermitian matrix is the sum of squares of its eigenvalues. -/
theorem sum_sq_eigenvalues_eq_frobenius {B : Matrix n n ℝ} (hB : B.IsHermitian) :
    ∑ i, (hB.eigenvalues i) ^ 2 = ∑ i, ∑ j, (B i j) ^ 2 := by
  rw [← trace_mul_self_eq_sum_sq hB, trace_mul_self_eq_sum_sq_entries hB]

/-! ## 3. The one-step inequality, spectral form -/

/-- **One-step inequality after congruence.**  For Hermitian `B` whose shifted eigenvalues
`1 + λᵢ` are positive and bounded above by `M ≥ 1`,
`log det (1 + B) ≤ tr B − (Σ λᵢ²)/(2M)`. -/
theorem log_det_one_add_le {B : Matrix n n ℝ} (hB : B.IsHermitian) {M : ℝ} (hM : 1 ≤ M)
    (hpos : ∀ i, 0 < 1 + hB.eigenvalues i) (hub : ∀ i, 1 + hB.eigenvalues i ≤ M) :
    Real.log (1 + B).det ≤ B.trace - (∑ i, (hB.eigenvalues i) ^ 2) / (2 * M) := by
  rw [det_one_add_eq_prod hB, Real.log_prod (fun i _ => ne_of_gt (hpos i)),
    trace_eq_sum_eigenvalues_real hB, Finset.sum_div, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum (fun i _ => ?_)
  have h := log_le_sub_one_sub_sq hM (hpos i) (hub i)
  simpa using h

end Spectral

/-! ## 4. The one-step inequality on the positive-definite cone -/

section Cone

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- Congruence by a symmetric matrix preserves Hermitian-ness. -/
theorem IsHermitian.conj' [DecidableEq n] {S H : Matrix n n ℝ} (hS : S.IsHermitian)
    (hH : H.IsHermitian) :
    (S * H * S).IsHermitian := by
  unfold Matrix.IsHermitian at *
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hS, hH, Matrix.mul_assoc]

/-- **The one-step log-det inequality.**  `S` is any symmetric congruence factor with
`S A S = 1` (think `S = A^{-1/2}`); `B = S H S` is then `A^{-1/2} H A^{-1/2}`:

`log det (A + H) ≤ log det A + tr (A⁻¹ H) − ‖A^{-1/2} H A^{-1/2}‖_F² / (2M)`

where `M ≥ 1` bounds the eigenvalues of `A^{-1/2}(A+H)A^{-1/2}` from above.  This is the discrete
replacement for Klartag's Lemma 3.3: summing it along the chain is the Riemann sum of
`−(1/2)∫ δ_s ds`, with no Itô formula and no local-martingale argument. -/
theorem log_det_add_le {A H S : Matrix n n ℝ} (hA : A.PosDef)
    (hS : S.IsHermitian) (hSA : S * A * S = 1) (hH : H.IsHermitian)
    {M : ℝ} (hM : 1 ≤ M)
    (hpos : ∀ i, 0 < 1 + (IsHermitian.conj' hS hH).eigenvalues i)
    (hub : ∀ i, 1 + (IsHermitian.conj' hS hH).eigenvalues i ≤ M) :
    Real.log (A + H).det ≤ Real.log A.det + (A⁻¹ * H).trace
      - (∑ i, ∑ j, ((S * H * S) i j) ^ 2) / (2 * M) := by
  have hB := IsHermitian.conj' hS hH
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
    rw [det_one_add_eq_prod hB]
    exact Finset.prod_pos (fun i _ => hpos i)
  rw [hdet, Real.log_mul (ne_of_gt hdetA) (ne_of_gt hposdet), htr,
    ← sum_sq_eigenvalues_eq_frobenius hB]
  linarith [log_det_one_add_le hB hM hpos hub]

/-- The paper's shape: with `κ ≥ 1` bounding the eigenvalues of `A^{-1/2}(A+H)A^{-1/2}`, the
quadratic gain is `‖A^{-1/2} H A^{-1/2}‖_F² / (2κ²)`. -/
theorem log_det_add_le_kappa {A H S : Matrix n n ℝ} (hA : A.PosDef)
    (hS : S.IsHermitian) (hSA : S * A * S = 1) (hH : H.IsHermitian)
    {κ : ℝ} (hκ : 1 ≤ κ)
    (hpos : ∀ i, 0 < 1 + (IsHermitian.conj' hS hH).eigenvalues i)
    (hub : ∀ i, 1 + (IsHermitian.conj' hS hH).eigenvalues i ≤ κ) :
    Real.log (A + H).det ≤ Real.log A.det + (A⁻¹ * H).trace
      - (∑ i, ∑ j, ((S * H * S) i j) ^ 2) / (2 * κ ^ 2) :=
  log_det_add_le hA hS hSA hH (by nlinarith : (1 : ℝ) ≤ κ ^ 2) hpos
    (fun i => le_trans (hub i) (by nlinarith))

end Cone

end Submission.L10

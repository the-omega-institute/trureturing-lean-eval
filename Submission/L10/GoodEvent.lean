import Submission.L10.GOETail2
import Submission.L10.OneStep
import Submission.L10.ChainDrift

/-!
# Gate L-10 — the good event, H5, and the one-step conditional inequality H1

This file discharges three of the hypotheses report 7 §8 left open.

* **The good event `S`** (`goodEvent`), the operator-norm bound on the accumulated Gaussian part
  of `A_N − a₀·Id`, with `μ(Sᶜ) ≤ 4 exp(−s²n)` from `GateL10.gaussian_opNormTail` (report 4), and
  its instantiation at the chain's scale `v = T/4`, `s = 1`, where the threshold is `6√(Tn)`.
* **H5** (`posDef_add_of_conj`, `oneStep_bounds_of_opNorm_le`): on the good event the conjugated
  increment `B = A^{-1/2} H A^{-1/2}` has `‖B‖_op ≤ δ < 1`, which gives both `(A + H) ≻ 0` — needed
  because `log det` is undefined off the cone (report 2 §5.5) — and the two eigenvalue hypotheses
  of `Submission.L10.log_det_add_le_kappa`, with `κ = 1 + δ`.
* **H1** (`condExp_step_le`): `ChainDrift.DriftInputs.step`, composed from the pointwise one-step
  bound and the two conditional laws H2 (centred increment) and H3 (conditional second moment).

`Increments.lean` (brief 6) exists in the tree but **report 6 has not landed**, so H2 and H3 are
taken here as named hypotheses with their exact signatures rather than imported; §4 of the
accompanying report says what has to match when brief 6 reports.
-/

namespace Submission.L10.GoodEvent

open MeasureTheory ProbabilityTheory Module Set Finset Matrix GateL10
open scoped ENNReal NNReal RealInnerProductSpace Matrix

/-! ## 1. An operator-norm toolkit for real symmetric matrices -/

section Toolkit

variable {n : ℕ}

/-- Every eigenvalue of a Hermitian matrix is bounded in absolute value by the `ℓ²` operator
norm.  Mathlib has the eigenvector basis (`Matrix.IsHermitian.mulVec_eigenvectorBasis`) but not
this bound. -/
theorem abs_eigenvalues_le_opNorm {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsHermitian)
    (i : Fin n) : |hB.eigenvalues i| ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) B‖ := by
  set T := Matrix.toEuclideanCLM (𝕜 := ℝ) B with hT
  set v : EuclideanSpace ℝ (Fin n) := hB.eigenvectorBasis i with hv
  have hv1 : ‖v‖ = 1 := hB.eigenvectorBasis.norm_eq_one i
  have hTv : T v = hB.eigenvalues i • v := by
    apply WithLp.ofLp_injective 2
    rw [hT, Matrix.ofLp_toEuclideanCLM]
    simpa using hB.mulVec_eigenvectorBasis i
  have hle := T.le_opNorm v
  rw [hTv, norm_smul, Real.norm_eq_abs, hv1, mul_one, mul_one] at hle
  exact hle

/-- The quadratic form is controlled by the operator norm. -/
theorem abs_inner_self_le_opNorm (B : Matrix (Fin n) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    |⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) B x⟫| ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) B‖ * ‖x‖ ^ 2 := by
  set T := Matrix.toEuclideanCLM (𝕜 := ℝ) B with hT
  calc |⟪x, T x⟫| ≤ ‖x‖ * ‖T x‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖T‖ * ‖x‖) := by gcongr; exact T.le_opNorm x
    _ = ‖T‖ * ‖x‖ ^ 2 := by ring

/-- Positive-definiteness read off the quadratic form on `EuclideanSpace`. -/
theorem posDef_of_inner_pos {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsHermitian)
    (h : ∀ x : EuclideanSpace ℝ (Fin n), x ≠ 0 →
      0 < ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) M x⟫) : M.PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨hM, fun x hx => ?_⟩
  have hx' : (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) ≠ 0 := by simpa using hx
  have hpos := h (WithLp.toLp 2 x) hx'
  rw [Matrix.inner_toEuclideanCLM] at hpos
  simpa using hpos

/-- Submultiplicativity of the `ℓ²` operator norm under congruence, obtained through
`toEuclideanCLM` rather than through the scoped `Matrix.Norms.L2Operator` instances. -/
theorem opNorm_conj_le (S H : Matrix (Fin n) (Fin n) ℝ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (S * H * S)‖
      ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S‖ ^ 2 * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) H‖ := by
  rw [map_mul, map_mul]
  calc ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S * Matrix.toEuclideanCLM (𝕜 := ℝ) H *
        Matrix.toEuclideanCLM (𝕜 := ℝ) S‖
      ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S * Matrix.toEuclideanCLM (𝕜 := ℝ) H‖ *
        ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S‖ := norm_mul_le _ _
    _ ≤ (‖Matrix.toEuclideanCLM (𝕜 := ℝ) S‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) H‖) *
        ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S‖ := by gcongr; exact norm_mul_le _ _
    _ = _ := by ring

/-- `1 + B` is positive definite as soon as `‖B‖_op < 1`. -/
theorem posDef_one_add {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsHermitian)
    {δ : ℝ} (hδ : δ < 1) (hnorm : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) B‖ ≤ δ) :
    (1 + B).PosDef := by
  refine posDef_of_inner_pos (Matrix.isHermitian_one.add hB) fun x hx => ?_
  have hxn : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
  have hsplit : ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (1 + B) x⟫
      = ‖x‖ ^ 2 + ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) B x⟫ := by
    rw [map_add, map_one]
    simp only [_root_.add_apply, one_apply_eq_self, inner_add_right,
      real_inner_self_eq_norm_sq]
  have hb := abs_inner_self_le_opNorm B x
  have hlow : -(δ * ‖x‖ ^ 2) ≤ ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) B x⟫ := by
    have h1 := (abs_le.mp hb).1
    nlinarith [sq_nonneg ‖x‖, hnorm]
  rw [hsplit]
  have hx2 : (0 : ℝ) < ‖x‖ ^ 2 := by positivity
  have hd : (0 : ℝ) < 1 - δ := by linarith
  nlinarith [hlow, hx2, hd]

/-- For real matrices, Hermitian is symmetric. -/
theorem isSymm_of_isHermitian {A : Matrix (Fin n) (Fin n) ℝ} (h : A.IsHermitian) : A.IsSymm := by
  ext i j
  have hij := congrFun (congrFun h.eq i) j
  simpa using hij

/-- `a₀·1 + G ⪰ (a₀ − ‖G‖)·1` in the quadratic-form sense: the shape the good event delivers,
since `A_k − a₀·Id` is the accumulated increment. -/
theorem lowerBound_of_opNorm_le {a₀ r : ℝ} {G : Matrix (Fin n) (Fin n) ℝ}
    (hG : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) G‖ ≤ r) (x : EuclideanSpace ℝ (Fin n)) :
    (a₀ - r) * ‖x‖ ^ 2
      ≤ ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (a₀ • (1 : Matrix (Fin n) (Fin n) ℝ) + G) x⟫ := by
  have hsplit : ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (a₀ • (1 : Matrix (Fin n) (Fin n) ℝ) + G) x⟫
      = a₀ * ‖x‖ ^ 2 + ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) G x⟫ := by
    rw [map_add, map_smul, map_one]
    simp only [_root_.add_apply, _root_.smul_apply, one_apply_eq_self, inner_add_right,
      real_inner_smul_right, real_inner_self_eq_norm_sq]
  have hb := abs_inner_self_le_opNorm G x
  have h1 := (abs_le.mp hb).1
  rw [hsplit]
  nlinarith [sq_nonneg ‖x‖, hG, norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℝ) G)]

/-- If `A ⪰ m` in the quadratic-form sense and `S A S = 1` with `S` symmetric, then
`‖S‖_op² ≤ 1/m`.  With `S = A^{-1/2}` this is `‖A^{-1/2}‖²_op = λ_min(A)⁻¹`. -/
theorem opNorm_sq_le_of_lowerBound {A S : Matrix (Fin n) (Fin n) ℝ}
    (hS : S.IsHermitian) (hSA : S * A * S = 1) {m : ℝ} (hm : 0 < m)
    (hAlb : ∀ x : EuclideanSpace ℝ (Fin n),
      m * ‖x‖ ^ 2 ≤ ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) A x⟫) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S‖ ^ 2 ≤ 1 / m := by
  set TS := Matrix.toEuclideanCLM (𝕜 := ℝ) S with hTS
  set TA := Matrix.toEuclideanCLM (𝕜 := ℝ) A with hTA
  have hSsymm := isSymm_of_isHermitian hS
  have key : ∀ x : EuclideanSpace ℝ (Fin n), ‖TS x‖ ≤ Real.sqrt (1 / m) * ‖x‖ := by
    intro x
    have hone : ⟪x, TS (TA (TS x))⟫ = ‖x‖ ^ 2 := by
      have h1 : Matrix.toEuclideanCLM (𝕜 := ℝ) (S * A * S) = TS * TA * TS := by
        rw [hTS, hTA, map_mul, map_mul]
      have h2 : Matrix.toEuclideanCLM (𝕜 := ℝ) (S * A * S) = 1 := by rw [hSA, map_one]
      have h3 : (TS * TA * TS : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) x = x := by
        rw [← h1, h2]; rfl
      rw [show TS (TA (TS x)) = (TS * TA * TS : _ →L[ℝ] _) x from rfl, h3,
        real_inner_self_eq_norm_sq]
    have hadj : ⟪x, TS (TA (TS x))⟫ = ⟪TS x, TA (TS x)⟫ :=
      (GateL10.inner_toEuclideanCLM_symm hSsymm x (TA (TS x))).symm
    have hlb := hAlb (TS x)
    have hmle : m * ‖TS x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
      rw [← hone, hadj]; exact hlb
    have hsq : ‖TS x‖ ^ 2 ≤ (Real.sqrt (1 / m) * ‖x‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hm]
      linarith
    have := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at this
  have hbd := ContinuousLinearMap.opNorm_le_bound TS (by positivity) key
  calc ‖TS‖ ^ 2 ≤ (Real.sqrt (1 / m)) ^ 2 := by
        nlinarith [norm_nonneg TS, Real.sqrt_nonneg (1 / m)]
    _ = 1 / m := Real.sq_sqrt (by positivity)

end Toolkit

/-! ## 2. H5 — positive definiteness and the `log_det_add_le_kappa` hypotheses -/

section H5

variable {n : ℕ}

/-- **H5, eigenvalue half.**  If the conjugated increment `B = S H S` has `‖B‖_op ≤ δ < 1` then
the two eigenvalue hypotheses of `Submission.L10.log_det_add_le_kappa` hold with `κ = 1 + δ`. -/
theorem oneStep_bounds_of_opNorm_le {H S : Matrix (Fin n) (Fin n) ℝ}
    (hS : S.IsHermitian) (hH : H.IsHermitian) {δ : ℝ} (hδ : δ < 1)
    (hnorm : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (S * H * S)‖ ≤ δ) :
    (∀ i, 0 < 1 + (IsHermitian.conj' hS hH).eigenvalues i)
      ∧ (∀ i, 1 + (IsHermitian.conj' hS hH).eigenvalues i ≤ 1 + δ) := by
  have hbd : ∀ i, |(IsHermitian.conj' hS hH).eigenvalues i| ≤ δ := fun i =>
    le_trans (abs_eigenvalues_le_opNorm (IsHermitian.conj' hS hH) i) hnorm
  constructor
  · intro i
    have := (abs_le.mp (hbd i)).1
    linarith
  · intro i
    have := (abs_le.mp (hbd i)).2
    linarith

/-- **H5, cone half.**  `A + H` stays positive definite.  The congruence `S(A+H)S = 1 + S H S`
transports `posDef_one_add` back, using that `S` is invertible with `S⁻¹ = A S = S A`. -/
theorem posDef_add_of_conj {A H S : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (hS : S.IsHermitian) (hSA : S * A * S = 1) (hH : H.IsHermitian)
    {δ : ℝ} (hδ : δ < 1)
    (hnorm : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (S * H * S)‖ ≤ δ) :
    (A + H).PosDef := by
  have hSS : S * S * A = 1 := by
    have h1 : (S * A) * S = 1 := hSA
    have h2 : S * (S * A) = 1 := _root_.mul_eq_one_comm.mp h1
    rw [← mul_assoc] at h2
    exact h2
  have hASS : A * (S * S) = 1 := _root_.mul_eq_one_comm.mp hSS
  have hcomm : S * A = A * S := by
    have h1 : S⁻¹ = A * S := Matrix.inv_eq_right_inv (by rw [← mul_assoc]; exact hSA)
    have h2 : S⁻¹ = S * A := Matrix.inv_eq_right_inv (by rw [← mul_assoc]; exact hSS)
    rw [← h1, ← h2]
  have hR : (A * S).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, hS.eq, hA.1.eq, hcomm]
  have hinj : Function.Injective (A * S).mulVec := by
    intro x y hxy
    have h := congrArg (fun z => S *ᵥ z) hxy
    simp only [Matrix.mulVec_mulVec] at h
    rwa [← mul_assoc, hSA, Matrix.one_mulVec, Matrix.one_mulVec] at h
  have hkey : (A * S) * (1 + S * H * S) * (A * S) = A + H := by
    have e1 : (A * S) * (A * S) = A := by
      calc (A * S) * (A * S) = A * (S * A * S) := by noncomm_ring
        _ = A := by rw [hSA, mul_one]
    have e2 : (A * S) * (S * H * S) * (A * S) = H := by
      calc (A * S) * (S * H * S) * (A * S) = (A * (S * S)) * H * (S * A * S) := by noncomm_ring
        _ = H := by rw [hASS, hSA, one_mul, mul_one]
    calc (A * S) * (1 + S * H * S) * (A * S)
        = (A * S) * (A * S) + (A * S) * (S * H * S) * (A * S) := by noncomm_ring
      _ = A + H := by rw [e1, e2]
  have h1B := posDef_one_add (IsHermitian.conj' hS hH) hδ hnorm
  have hcong := Matrix.PosDef.conjTranspose_mul_mul_same h1B hinj
  rwa [hR.eq, hkey] at hcong

/-- **The composed one-step bound.**  On the good event (`‖S H S‖_op ≤ δ < 1`) the log-determinant
obeys Klartag's Lemma 3.3 in discrete form with `κ = 1 + δ`, and `A + H` is still in the cone. -/
theorem log_det_step_le {A H S : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (hS : S.IsHermitian) (hSA : S * A * S = 1) (hH : H.IsHermitian)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ < 1)
    (hnorm : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (S * H * S)‖ ≤ δ) :
    (A + H).PosDef ∧
      Real.log (A + H).det ≤ Real.log A.det + (A⁻¹ * H).trace
        - (∑ i, ∑ j, ((S * H * S) i j) ^ 2) / (2 * (1 + δ) ^ 2) := by
  obtain ⟨hpos, hub⟩ := oneStep_bounds_of_opNorm_le hS hH hδ hnorm
  exact ⟨posDef_add_of_conj hA hS hSA hH hδ hnorm,
    log_det_add_le_kappa hA hS hSA hH (by linarith) hpos hub⟩

/-- **H5, end to end.**  From what the good event supplies — a lower bound `m` on `A`'s quadratic
form and an operator-norm bound `η` on the increment — the conjugated increment obeys
`‖A^{-1/2} H A^{-1/2}‖_op ≤ η/m`, so if `η/m ≤ δ < 1` both halves of H5 hold and the one-step
log-det inequality applies with `κ = 1 + δ`. -/
theorem oneStep_of_good {A H S : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (hS : S.IsHermitian) (hSA : S * A * S = 1) (hH : H.IsHermitian)
    {m η δ : ℝ} (hm : 0 < m)
    (hAlb : ∀ x : EuclideanSpace ℝ (Fin n),
      m * ‖x‖ ^ 2 ≤ ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) A x⟫)
    (hHub : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) H‖ ≤ η)
    (hδ : η / m ≤ δ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    (A + H).PosDef ∧
      Real.log (A + H).det ≤ Real.log A.det + (A⁻¹ * H).trace
        - (∑ i, ∑ j, ((S * H * S) i j) ^ 2) / (2 * (1 + δ) ^ 2) := by
  have hSnorm := opNorm_sq_le_of_lowerBound hS hSA hm hAlb
  have hη : 0 ≤ η := le_trans (norm_nonneg _) hHub
  have hconj : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (S * H * S)‖ ≤ δ := by
    refine le_trans (opNorm_conj_le S H) (le_trans ?_ hδ)
    calc ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S‖ ^ 2 * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) H‖
        ≤ (1 / m) * η := by
          exact mul_le_mul hSnorm hHub (norm_nonneg _) (by positivity)
      _ = η / m := by ring
  exact log_det_step_le hA hS hSA hH hδ0 hδ1 hconj

end H5

/-! ## 3. The good event -/

section Good

variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}

/-- The good event of Klartag's Proposition 3.4 (p. 16, eq. 43): the accumulated Gaussian part of
`A_N − a₀·Id` has operator norm at most `r`. -/
def goodEvent (G : Ω → Matrix (Fin n) (Fin n) ℝ) (r : ℝ) : Set Ω :=
  {ω | ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (G ω)‖ ≤ r}

/-- **`μ(Sᶜ) ≤ 4 exp(−s²n)`**, directly from `GateL10.gaussian_opNormTail`. -/
theorem measureReal_compl_goodEvent_le (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Ω → Matrix (Fin n) (Fin n) ℝ) (v : ℝ≥0) (hv : 0 < v)
    (hindep : iIndepFun (fun (p : Fin n × Fin n) (ω : Ω) => B ω p.1 p.2) P)
    (hlaw : ∀ i j, P.map (fun ω => B ω i j) = gaussianReal 0 v)
    (s : ℝ) (hs : 1 ≤ s) :
    P.real (goodEvent (fun ω => B ω + (B ω)ᵀ) (12 * Real.sqrt v * s * Real.sqrt n))ᶜ
      ≤ 4 * Real.exp (-(s ^ 2 * n)) := by
  refine le_trans (measureReal_mono ?_ (measure_ne_top P _))
    (gaussian_opNormTail P n B v hv hindep hlaw s hs)
  intro ω hω
  have hω' : ¬ (‖Matrix.toEuclideanCLM (𝕜 := ℝ) (B ω + (B ω)ᵀ)‖
      ≤ 12 * Real.sqrt v * s * Real.sqrt n) := hω
  exact le_of_lt (not_le.mp hω')

/-- The threshold at the chain's scale: with `v = T/4` and `s = 1` it is `6√(Tn)`. -/
theorem threshold_chainScale {T : ℝ} (hT : 0 ≤ T) (v : ℝ≥0) (hv : (v : ℝ) = T / 4) :
    12 * Real.sqrt v * 1 * Real.sqrt n = 6 * Real.sqrt (T * n) := by
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hv, Real.sqrt_div hT, h4, Real.sqrt_mul hT]
  ring

/-- **The good event at the chain's scale.**  The increments of the chain after time `T` form
`B + Bᵀ` with the entries of `B` i.i.d. `N(0, T/4)`; on the good event the Gaussian part of
`A_N − a₀·Id` has operator norm at most `6√(Tn)`, and the event fails with probability at most
`4 e^{−n}` — so the cost `n²·μ(Sᶜ)` of Proposition 3.4's truncation is `4 n² e^{−n} = o(1)`.
With `T = ChainDrift.horizon n = 16 log n / n²` the threshold is `24 √(log n / n) = o(1)`, which is
what report 7 §6.2's constraint (G) asks of the Gaussian part. -/
theorem measureReal_compl_goodEvent_chainScale (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Ω → Matrix (Fin n) (Fin n) ℝ) {T : ℝ} (hT : 0 ≤ T) (v : ℝ≥0) (hv : (v : ℝ) = T / 4)
    (hvpos : 0 < v)
    (hindep : iIndepFun (fun (p : Fin n × Fin n) (ω : Ω) => B ω p.1 p.2) P)
    (hlaw : ∀ i j, P.map (fun ω => B ω i j) = gaussianReal 0 v) :
    P.real (goodEvent (fun ω => B ω + (B ω)ᵀ) (6 * Real.sqrt (T * n)))ᶜ
      ≤ 4 * Real.exp (-(n : ℝ)) := by
  have h := measureReal_compl_goodEvent_le P B v hvpos hindep hlaw 1 le_rfl
  rw [threshold_chainScale hT v hv] at h
  simpa using h

/-- `6√(Tn) = 24√(log n / n)` at `T = ChainDrift.horizon n`: the good-event threshold is `o(1)`. -/
theorem threshold_horizon {n : ℕ} (hn : 0 < n) :
    6 * Real.sqrt (ChainDrift.horizon n * n) = 24 * Real.sqrt (Real.log n / n) := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hval : ChainDrift.horizon n * (n : ℝ) = 16 * (Real.log n / n) := by
    rw [ChainDrift.horizon]
    field_simp
  rw [hval, Real.sqrt_mul (by norm_num), show Real.sqrt 16 = 4 by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  ring

end Good

/-! ## 4. H1 — the one-step conditional inequality -/

section H1

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- **H1 = `ChainDrift.DriftInputs.step`.**  Composed from

* `hpt`, the pointwise one-step bound — `log_det_step_le` above, read at `D k = log det A_k`,
  `tr = ⟪A_k⁻¹, π_kξ_k⟫`, `quad = ‖A_k^{-1/2} π_kξ_k A_k^{-1/2}‖_F²/(2(1+δ)²)`;
* `h2` (**H2**), the centred increment: `μ[tr | ℱ] =ᵐ 0`;
* `h3` (**H3**), the conditional second moment: `μ[quad | ℱ] =ᵐ κ · N`.

Nothing else is used, and no property of the chain enters: `D`, `N`, `err` are arbitrary. -/
theorem condExp_step_le {ℱ : MeasurableSpace Ω} (hℱ : ℱ ≤ m0) [SigmaFinite (μ.trim hℱ)]
    {Dk Dk1 Nk errk tr quad : Ω → ℝ} {κ : ℝ}
    (hpt : ∀ᵐ ω ∂μ, Dk1 ω ≤ Dk ω + tr ω - quad ω + errk ω)
    (hDkm : StronglyMeasurable[ℱ] Dk) (herrm : StronglyMeasurable[ℱ] errk)
    (iDk1 : Integrable Dk1 μ) (iDk : Integrable Dk μ) (itr : Integrable tr μ)
    (iquad : Integrable quad μ) (ierr : Integrable errk μ)
    (h2 : μ[tr|ℱ] =ᵐ[μ] 0)
    (h3 : μ[quad|ℱ] =ᵐ[μ] fun ω => κ * Nk ω) :
    μ[Dk1|ℱ] ≤ᵐ[μ] fun ω => Dk ω - κ * Nk ω + errk ω := by
  have iSum : Integrable (fun ω => Dk ω + tr ω - quad ω + errk ω) μ :=
    ((iDk.add itr).sub iquad).add ierr
  have hmono := condExp_mono (m := ℱ) iDk1 iSum hpt
  have hexp : μ[fun ω => Dk ω + tr ω - quad ω + errk ω|ℱ]
      =ᵐ[μ] fun ω => Dk ω - κ * Nk ω + errk ω := by
    have e1 : μ[fun ω => Dk ω + tr ω - quad ω + errk ω|ℱ]
        =ᵐ[μ] μ[fun ω => Dk ω + tr ω - quad ω|ℱ] + μ[errk|ℱ] :=
      condExp_add ((iDk.add itr).sub iquad) ierr ℱ
    have e2 : μ[fun ω => Dk ω + tr ω - quad ω|ℱ]
        =ᵐ[μ] μ[fun ω => Dk ω + tr ω|ℱ] - μ[quad|ℱ] :=
      condExp_sub (iDk.add itr) iquad ℱ
    have e3 : μ[fun ω => Dk ω + tr ω|ℱ] =ᵐ[μ] μ[Dk|ℱ] + μ[tr|ℱ] := condExp_add iDk itr ℱ
    have hD : μ[Dk|ℱ] = Dk := condExp_of_stronglyMeasurable hℱ hDkm iDk
    have hE : μ[errk|ℱ] = errk := condExp_of_stronglyMeasurable hℱ herrm ierr
    filter_upwards [e1, e2, e3, h2, h3] with ω a1 a2 a3 a2' a3'
    simp only [Pi.add_apply, Pi.sub_apply] at a1 a2 a3
    rw [a1, a2, a3, hD, hE]
    simp only [Pi.zero_apply] at a2' ⊢
    rw [a2', a3']
    ring
  filter_upwards [hmono, hexp] with ω hm he
  rw [← he]
  exact hm

/-- **H1 in the exact shape of `ChainDrift.DriftInputs.step`.**  This is the field the wiring
brief has to supply; everything else in `DriftInputs` is integrability.  Note that no
measurability of `N` is needed: `h3` already delivers the conditional expectation of the
quadratic term in the required form. -/
theorem driftInputs_step {ℱ : ℕ → MeasurableSpace Ω} (hℱ : ∀ k, ℱ k ≤ m0)
    [∀ k, SigmaFinite (μ.trim (hℱ k))]
    {D N err tr quad : ℕ → Ω → ℝ} {κ : ℝ} {m : ℕ}
    (hpt : ∀ k, k < m → ∀ᵐ ω ∂μ, D (k + 1) ω ≤ D k ω + tr k ω - quad k ω + err k ω)
    (hDm : ∀ k, StronglyMeasurable[ℱ k] (D k))
    (herrm : ∀ k, StronglyMeasurable[ℱ k] (err k))
    (iD : ∀ k, Integrable (D k) μ) (itr : ∀ k, Integrable (tr k) μ)
    (iquad : ∀ k, Integrable (quad k) μ) (ierr : ∀ k, Integrable (err k) μ)
    (h2 : ∀ k, μ[tr k|ℱ k] =ᵐ[μ] 0)
    (h3 : ∀ k, μ[quad k|ℱ k] =ᵐ[μ] fun ω => κ * N k ω) :
    ∀ k, k < m → μ[D (k + 1)|ℱ k] ≤ᵐ[μ] fun ω => D k ω - κ * N k ω + err k ω :=
  fun k hk => condExp_step_le (hℱ k) (hpt k hk) (hDm k) (herrm k) (iD (k + 1)) (iD k)
    (itr k) (iquad k) (ierr k) (h2 k) (h3 k)

end H1

end Submission.L10.GoodEvent

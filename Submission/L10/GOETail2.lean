import Submission.L10.GOETail

/-!
# Gate L-10, hinge 3 — completing the operator-norm tail (steps 3–8)

This file completes `Submission/L10/GOETail.lean` (brief 1, report
`research/gate-l10/reports/1-goe-tail.md`), whose statements are frozen and are imported here.

The route taken is the **symmetrised** one: the random matrix is `B + Bᵀ` with the entries of `B`
independent over the full product `Fin n × Fin n`. This removes the `i ≤ j` re-indexing from
step (3), as predicted in report 1 §1b: `⟪(B + Bᵀ) x, x⟫` is *already* a sum of independent terms
over the full product type (`GateL10.inner_symmetrized`), and the only reindexing left is a single
`Finset.sum_comm`.

**Correction to report 1.** `GateL10.OpNormTail` and `GateL10.OpNormTailSymmetrized` as stated
there are **false at `c = 0`**: the threshold `C √c s √n` collapses to `0`, the event becomes
everything and has probability `1`, while the bound `4 exp (-s² n)` drops below `1` as soon as
`n ≥ 2`. The hypothesis `0 < c` is missing. It is supplied here; `OpNormTailSymmetrized'` is the
corrected statement and `opNormTailSymmetrized'_twelve` proves it with `C = 12`.

Main results:
* `hasSubgaussianMGF_of_hasLaw_gaussianReal` — centred Gaussians are sub-Gaussian (step 3d).
* `hasSubgaussianMGF_of_map_gaussianReal` — the map bridge at nonzero variance.
* `inner_symmetrized` — the quadratic form as a sum over the full product (step 3a).
* `hasSubgaussianMGF_quadForm` — that sum is sub-Gaussian with parameter `4c` (step 3c).
* `opNormTail_symmetrized` — the tail with `C = 12` (steps 4, 5, 6, 8).
* `goe_opNormTail` — Klartag's Corollary 3.2 shape at the GOE normalisation (step 7).
-/

namespace GateL10

open MeasureTheory ProbabilityTheory Module Set Finset
open scoped ENNReal NNReal RealInnerProductSpace Matrix

/-! ## Step 3d. Centred Gaussians are sub-Gaussian -/

/-- A real random variable whose law is `N(0, v)` has a sub-Gaussian MGF with parameter `v`.
Mathlib has `mgf_gaussianReal` and `integrable_exp_mul_gaussianReal` but no bridge to
`HasSubgaussianMGF`, which occurs in no file other than `Probability/Moments/SubGaussian.lean`. -/
theorem hasSubgaussianMGF_of_hasLaw_gaussianReal {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {v : ℝ≥0} (hX : HasLaw X (gaussianReal 0 v) P) :
    HasSubgaussianMGF X v P := by
  refine ⟨?_, ?_⟩
  · intro t
    have h1 : Integrable (fun z : ℝ => Real.exp (t * z)) (P.map X) := by
      rw [hX.map_eq]; exact integrable_exp_mul_gaussianReal t
    rwa [integrable_map_measure (by fun_prop) hX.aemeasurable] at h1
  · intro t
    exact le_of_eq (by rw [mgf_gaussianReal hX t]; simp)

/-- A nondegenerate Gaussian map equality also certifies a.e. measurability: a nonmeasurable
map has a Dirac pushforward, whereas a Gaussian with nonzero variance has no atoms. -/
theorem hasSubgaussianMGF_of_map_gaussianReal {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {v : ℝ≥0} (hX : P.map X = gaussianReal 0 v) (hv : v ≠ 0) :
    HasSubgaussianMGF X v P := by
  have hP : P ≠ 0 := by
    intro hP
    apply IsProbabilityMeasure.ne_zero (gaussianReal 0 v)
    simpa [hP] using hX.symm
  have hXm : AEMeasurable X P := by
    by_contra hm
    have hdirac := Measure.map_of_not_aemeasurable_of_ne_zero hm hP
    have := nullSingletonClass_gaussianReal (μ := (0 : ℝ)) hv
    have hsingle := congrArg (fun μ : Measure ℝ => μ {Classical.ofNonempty})
      (hdirac.symm.trans hX)
    simp at hsingle
  exact hasSubgaussianMGF_of_hasLaw_gaussianReal ⟨hXm, hX⟩

/-! ## Step 3a. The quadratic form of a symmetrised matrix -/

/-- The bilinear form of a symmetric matrix is symmetric. -/
theorem dotProduct_mulVec_comm {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (u v : Fin n → ℝ) : u ⬝ᵥ A *ᵥ v = v ⬝ᵥ A *ᵥ u := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  linear_combination (u b * v a) * hA.apply a b

/-- `toEuclideanCLM` of a symmetric real matrix is self-adjoint, in the elementary form
`GateL10.opNorm_le_of_net` consumes. -/
theorem inner_toEuclideanCLM_symm {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (x y : EuclideanSpace ℝ (Fin n)) :
    ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) A x, y⟫ = ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) A y⟫ := by
  rw [real_inner_comm, Matrix.inner_toEuclideanCLM, Matrix.inner_toEuclideanCLM]
  exact dotProduct_mulVec_comm hA _ _

/-- `B + Bᵀ` is symmetric. -/
theorem isSymm_add_transpose {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) : (B + Bᵀ).IsSymm := by
  unfold Matrix.IsSymm
  rw [Matrix.transpose_add, Matrix.transpose_transpose]
  exact add_comm _ _

/-- The quadratic form of the symmetrised matrix, as a linear form in the independent entries
of `B`. -/
noncomputable def quadForm {Ω : Type*} {n : ℕ} (B : Ω → Matrix (Fin n) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (ω : Ω) : ℝ :=
  ∑ p : Fin n × Fin n, (2 * x p.1 * x p.2) * B ω p.1 p.2

/-- **Step 3a.** The quadratic form of `B + Bᵀ` is a sum over the *full* product
`Fin n × Fin n` of the independent entries of `B`, with coefficients `2 x_i x_j`. No `i ≤ j`
filter and no `Prod.swap` reindexing: the only reindexing is one `Finset.sum_comm`. -/
theorem inner_symmetrized {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (B + Bᵀ) x, x⟫
      = ∑ p : Fin n × Fin n, (2 * x p.1 * x p.2) * B p.1 p.2 := by
  rw [real_inner_comm, Matrix.inner_toEuclideanCLM, Fintype.sum_prod_type]
  simp only [dotProduct, Matrix.mulVec, Matrix.add_apply, Matrix.transpose_apply, Finset.mul_sum]
  have expand : ∀ i : Fin n, ∑ j, x i * ((B i j + B j i) * x j)
      = (∑ j, x i * B i j * x j) + (∑ j, x i * B j i * x j) := by
    intro i
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [Finset.sum_congr rfl fun i _ => expand i, Finset.sum_add_distrib]
  have swap : ∑ i, ∑ j, x i * B j i * x j = ∑ i, ∑ j, x i * B i j * x j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [swap, ← two_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-! ## Step 3c. The quadratic form is sub-Gaussian with parameter `4c` -/

/-- A unit vector of `EuclideanSpace ℝ (Fin n)` has coordinate squares summing to `1`. -/
theorem sum_sq_coord_eq_one {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ = 1) :
    ∑ i, x i ^ 2 = 1 := by
  have h := EuclideanSpace.norm_sq_eq (𝕜 := ℝ) x
  rw [hx] at h
  simp only [Real.norm_eq_abs, sq_abs] at h
  linarith [h]

/-- **Step 3c.** For a unit vector `x`, the linear form `∑ p, (2 x_{p.1} x_{p.2}) B_{p.1 p.2}`
in the independent entries of `B` is sub-Gaussian with parameter `4c`. The coefficient bound is
`GateL10.sum_sq_coeff_le`; the closure properties are `HasSubgaussianMGF.const_mul` and
`.sum_of_iIndepFun`, and the parameter is relaxed by `GateL10.hasSubgaussianMGF_mono`. -/
theorem hasSubgaussianMGF_quadForm {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n : ℕ} (B : Ω → Matrix (Fin n) (Fin n) ℝ) {c : ℝ≥0}
    (hindep : iIndepFun (fun (p : Fin n × Fin n) (ω : Ω) => B ω p.1 p.2) P)
    (hsub : ∀ i j, HasSubgaussianMGF (fun ω => B ω i j) c P)
    (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ = 1) :
    HasSubgaussianMGF (quadForm B x) (4 * c) P := by
  classical
  have hindep' : iIndepFun
      (fun (p : Fin n × Fin n) (ω : Ω) => (2 * x p.1 * x p.2) * B ω p.1 p.2) P :=
    hindep.comp (fun p z => (2 * x p.1 * x p.2) * z)
      (fun p => measurable_const_mul (2 * x p.1 * x p.2))
  have hsubG : ∀ p ∈ (Finset.univ : Finset (Fin n × Fin n)),
      HasSubgaussianMGF (fun ω => (2 * x p.1 * x p.2) * B ω p.1 p.2)
        (⟨(2 * x p.1 * x p.2) ^ 2, sq_nonneg _⟩ * c) P :=
    fun p _ => (hsub p.1 p.2).const_mul (2 * x p.1 * x p.2)
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun hindep' hsubG
  refine hasSubgaussianMGF_mono hsum ?_
  have hcoeff : ∑ p : Fin n × Fin n, (2 * x p.1 * x p.2) ^ 2 ≤ 4 :=
    sum_sq_coeff_le x (sum_sq_coord_eq_one x hx)
  rw [← NNReal.coe_le_coe, NNReal.coe_sum]
  have hcoe : ∀ p : Fin n × Fin n,
      ((⟨(2 * x p.1 * x p.2) ^ 2, sq_nonneg _⟩ * c : ℝ≥0) : ℝ)
        = (2 * x p.1 * x p.2) ^ 2 * (c : ℝ) := fun _ => rfl
  simp only [hcoe]
  rw [← Finset.sum_mul]
  have h4 : ((4 * c : ℝ≥0) : ℝ) = 4 * (c : ℝ) := by push_cast; ring
  rw [h4]
  exact mul_le_mul_of_nonneg_right hcoeff c.coe_nonneg

/-! ## The `c = 0` defect in the statements reported by brief 1 -/

/-- `4 * exp (-4) < 1`, the numeric core of the counterexample below. -/
theorem four_mul_exp_neg_four_lt_one : 4 * Real.exp (-4) < 1 := by
  have h5 : (5 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hpos : (0 : ℝ) < Real.exp 4 := Real.exp_pos 4
  have hinv : Real.exp 4 * (Real.exp 4)⁻¹ = 1 := mul_inv_cancel₀ hpos.ne'
  rw [Real.exp_neg]
  nlinarith

/-- **The statement `GateL10.OpNormTailSymmetrized` reported by brief 1 is false**, for every
constant `C`, because it omits `0 < c`. Counterexample: `n = 1`, `B ≡ 0`, `c = 0`, `s = 2` over
the one-point probability space. The threshold `C √c s √n` is then `0`, so the event is all of
`Ω` and has probability `1`, while the claimed bound `4 exp (-s² n)` is `4 exp (-4) < 1`.
`GateL10.OpNormTailSymmetrized'` adds the missing hypothesis. -/
theorem not_opNormTailSymmetrized (C : ℝ) : ¬ OpNormTailSymmetrized C := by
  intro h
  have key := h (Ω := Unit) (Measure.dirac ()) 1 (fun _ => 0) 0
    (fun _ _ => measurable_const) iIndepFun.of_subsingleton
    (fun _ _ => by simp) 2 (by norm_num)
  simp only [NNReal.coe_zero, Real.sqrt_zero, mul_zero, zero_mul, Matrix.transpose_zero,
    add_zero, map_zero, norm_zero, le_refl, Set.ofPred_true] at key
  norm_num at key
  linarith [four_mul_exp_neg_four_lt_one]

/-- **The statement `GateL10.OpNormTail` reported by brief 1 is false** for the same reason:
the same `n = 1`, `A ≡ 0`, `c = 0`, `s = 2` counterexample. -/
theorem not_opNormTail (C : ℝ) : ¬ OpNormTail C := by
  intro h
  have key := h (Ω := Unit) (Measure.dirac ()) 1 (fun _ => 0) 0
    (fun _ => Matrix.transpose_zero) (fun _ _ => measurable_const) iIndepFun.of_subsingleton
    (fun _ _ _ => by simp) 2 (by norm_num)
  simp only [NNReal.coe_zero, Real.sqrt_zero, mul_zero, zero_mul, map_zero, norm_zero, le_refl,
    Set.ofPred_true] at key
  norm_num at key
  linarith [four_mul_exp_neg_four_lt_one]

/-! ## Steps 4–6, 8. The tail -/

/-- The corrected statement of Klartag's Corollary 3.2 in the symmetrised form: the `0 < c`
that `GateL10.OpNormTailSymmetrized` is missing. -/
def OpNormTailSymmetrized' (C : ℝ) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (B : Ω → Matrix (Fin n) (Fin n) ℝ) (c : ℝ≥0), 0 < c →
    ProbabilityTheory.iIndepFun (fun (p : Fin n × Fin n) (ω : Ω) => B ω p.1 p.2) P →
    (∀ i j : Fin n, ProbabilityTheory.HasSubgaussianMGF (fun ω => B ω i j) c P) →
    ∀ s : ℝ, 1 ≤ s →
      P.real {ω | C * Real.sqrt c * s * Real.sqrt n ≤
        ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (B ω + (B ω)ᵀ)‖} ≤ 4 * Real.exp (-(s ^ 2 * n))

/-- **The tail, with `C = 12`.** Steps 4 (union bound over the `ε = 1/4` net), 5 (the constant),
6 (assembly) and 8 (`n = 0`). -/
theorem opNormTail_symmetrized {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ) (B : Ω → Matrix (Fin n) (Fin n) ℝ) (c : ℝ≥0) (hc : 0 < c)
    (hindep : iIndepFun (fun (p : Fin n × Fin n) (ω : Ω) => B ω p.1 p.2) P)
    (hsub : ∀ i j, HasSubgaussianMGF (fun ω => B ω i j) c P)
    (s : ℝ) (hs : 1 ≤ s) :
    P.real {ω | 12 * Real.sqrt c * s * Real.sqrt n ≤
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (B ω + (B ω)ᵀ)‖} ≤ 4 * Real.exp (-(s ^ 2 * n)) := by
  classical
  have hs0 : (0 : ℝ) < s := lt_of_lt_of_le one_pos hs
  have hcR : (0 : ℝ) < (c : ℝ) := hc
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- step 8: `n = 0`; the space is trivial and the threshold is `0`
    have hset : {ω : Ω | 12 * Real.sqrt (c : ℝ) * s * Real.sqrt ((0 : ℕ) : ℝ) ≤
        ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (B ω + (B ω)ᵀ)‖} = Set.univ := by
      ext ω; simp
    rw [hset]
    have huniv : P.real (Set.univ : Set Ω) = 1 := by
      rw [measureReal_def, measure_univ, ENNReal.toReal_one]
    rw [huniv]
    simp
  -- `n ≥ 1`
  have hnt : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; exact hn)
  obtain ⟨N, hN1, hN2, hN3⟩ :=
    exists_net (E := EuclideanSpace ℝ (Fin n)) volume (ε := 1 / 4) (by norm_num)
  rw [finrank_euclideanSpace_fin] at hN2
  -- the net is nonempty
  obtain ⟨z, hz⟩ := exists_ne (0 : EuclideanSpace ℝ (Fin n))
  have hzn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hz1 : ‖(‖z‖⁻¹ • z : EuclideanSpace ℝ (Fin n))‖ = 1 := by
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z),
      inv_mul_cancel₀ hzn]
  obtain ⟨y₀, hy₀, -⟩ := hN3 _ hz1
  have hNne : N.Nonempty := ⟨y₀, hy₀⟩
  set u : ℝ := 6 * Real.sqrt (c : ℝ) * s * Real.sqrt (n : ℝ) with hu
  have hu0 : 0 ≤ u := by
    rw [hu]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hs0.le)
      (Real.sqrt_nonneg _)
  have hQsub : ∀ x ∈ N, HasSubgaussianMGF (quadForm B x) (4 * c) P := fun x hx =>
    hasSubgaussianMGF_quadForm B hindep hsub x (hN1 x hx)
  -- step 4a: the bad event sits inside the union over the net
  have hcontain : {ω | 12 * Real.sqrt (c : ℝ) * s * Real.sqrt (n : ℝ) ≤
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (B ω + (B ω)ᵀ)‖} ⊆ ⋃ x ∈ N, {ω | u ≤ |quadForm B x ω|} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    have hM0 : 0 ≤ N.sup' hNne (fun y => |quadForm B y ω|) :=
      le_trans (abs_nonneg (quadForm B y₀ ω))
        (Finset.le_sup' (fun y => |quadForm B y ω|) hy₀)
    have hbound : ∀ y ∈ N, |⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (B ω + (B ω)ᵀ) y, y⟫|
        ≤ N.sup' hNne (fun y => |quadForm B y ω|) := by
      intro y hy
      rw [inner_symmetrized]
      exact Finset.le_sup' (fun y => |quadForm B y ω|) hy
    have hnet := opNorm_le_of_net (E := EuclideanSpace ℝ (Fin n))
      (by norm_num : (0 : ℝ) < 1 / 4) N hN1 hN3 _
      (inner_toEuclideanCLM_symm (isSymm_add_transpose (B ω))) hM0 hbound
    have key : u ≤ N.sup' hNne (fun y => |quadForm B y ω|) := by rw [hu]; linarith
    exact (Finset.le_sup'_iff hNne).mp key
  -- step 4b: the two-sided Chernoff bound at each net point
  have hterm : ∀ x ∈ N, P.real {ω | u ≤ |quadForm B x ω|}
      ≤ 2 * Real.exp (-u ^ 2 / (2 * ((4 * c : ℝ≥0) : ℝ))) := by
    intro x hx
    have hsplit : {ω | u ≤ |quadForm B x ω|}
        ⊆ {ω | u ≤ quadForm B x ω} ∪ {ω | u ≤ (-quadForm B x) ω} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω
      rcases abs_cases (quadForm B x ω) with ⟨h1, -⟩ | ⟨h1, -⟩
      · rw [h1] at hω; exact Or.inl hω
      · rw [h1] at hω; exact Or.inr hω
    calc P.real {ω | u ≤ |quadForm B x ω|}
        ≤ P.real ({ω | u ≤ quadForm B x ω} ∪ {ω | u ≤ (-quadForm B x) ω}) :=
          measureReal_mono hsplit (measure_ne_top P _)
      _ ≤ P.real {ω | u ≤ quadForm B x ω} + P.real {ω | u ≤ (-quadForm B x) ω} :=
          measureReal_union_le _ _
      _ ≤ Real.exp (-u ^ 2 / (2 * ((4 * c : ℝ≥0) : ℝ)))
            + Real.exp (-u ^ 2 / (2 * ((4 * c : ℝ≥0) : ℝ))) :=
          add_le_add ((hQsub x hx).measure_ge_le hu0) ((hQsub x hx).neg.measure_ge_le hu0)
      _ = 2 * Real.exp (-u ^ 2 / (2 * ((4 * c : ℝ≥0) : ℝ))) := by ring
  -- step 5: the exponent
  have hexp : -u ^ 2 / (2 * ((4 * c : ℝ≥0) : ℝ)) = -(9 / 2 * s ^ 2 * n) := by
    have h1 : Real.sqrt (c : ℝ) ^ 2 = (c : ℝ) := Real.sq_sqrt c.coe_nonneg
    have h2 : Real.sqrt ((n : ℕ) : ℝ) ^ 2 = ((n : ℕ) : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
    have h3 : u ^ 2 = 36 * (c : ℝ) * s ^ 2 * n := by
      rw [hu, show (6 * Real.sqrt (c : ℝ) * s * Real.sqrt ((n : ℕ) : ℝ)) ^ 2
        = 36 * Real.sqrt (c : ℝ) ^ 2 * s ^ 2 * Real.sqrt ((n : ℕ) : ℝ) ^ 2 by ring, h1, h2]
    rw [h3]
    have hcne : (c : ℝ) ≠ 0 := ne_of_gt hcR
    push_cast
    field_simp
    ring
  -- step 6: assembly
  calc P.real {ω | 12 * Real.sqrt (c : ℝ) * s * Real.sqrt (n : ℝ) ≤
        ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (B ω + (B ω)ᵀ)‖}
      ≤ P.real (⋃ x ∈ N, {ω | u ≤ |quadForm B x ω|}) :=
        measureReal_mono hcontain (measure_ne_top P _)
    _ ≤ ∑ x ∈ N, P.real {ω | u ≤ |quadForm B x ω|} := measureReal_biUnion_finset_le N _
    _ ≤ ∑ _x ∈ N, 2 * Real.exp (-(9 / 2 * s ^ 2 * n)) := by
        refine Finset.sum_le_sum fun x hx => ?_
        rw [← hexp]
        exact hterm x hx
    _ = (N.card : ℝ) * (2 * Real.exp (-(9 / 2 * s ^ 2 * n))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (9 : ℝ) ^ n * (2 * Real.exp (-(9 / 2 * s ^ 2 * n))) := by
        have h9 : (1 + 2 / (1 / 4 : ℝ)) = 9 := by norm_num
        rw [h9] at hN2
        exact mul_le_mul_of_nonneg_right hN2 (by positivity)
    _ = 2 * ((9 : ℝ) ^ n * Real.exp (-(9 / 2 * s ^ 2 * n))) := by ring
    _ ≤ 2 * Real.exp (-(s ^ 2 * n)) :=
        mul_le_mul_of_nonneg_left (union_bound_arith hs) (by norm_num)
    _ ≤ 4 * Real.exp (-(s ^ 2 * n)) := by
        have := Real.exp_pos (-(s ^ 2 * (n : ℝ)))
        linarith

/-- The goal of brief 4, in the symmetrised form: `C = 12` works. -/
theorem opNormTailSymmetrized'_twelve : OpNormTailSymmetrized' 12 := by
  unfold OpNormTailSymmetrized'
  intro Ω _ P _ n B c hc hindep hsub s hs
  exact opNormTail_symmetrized P n B c hc hindep hsub s hs

/-! ## Step 7. The GOE instantiation -/

/-- The Gaussian case at a general variance, which is the form the discrete chain of hinge 1
plugs into: its increment after time `t` is a standard Gaussian on `R^{n×n}_sym` scaled by `√t`,
i.e. `B + Bᵀ` with the entries of `B` i.i.d. `N(0, t/4)`. -/
theorem gaussian_opNormTail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ) (B : Ω → Matrix (Fin n) (Fin n) ℝ) (v : ℝ≥0) (hv : 0 < v)
    (hindep : iIndepFun (fun (p : Fin n × Fin n) (ω : Ω) => B ω p.1 p.2) P)
    (hlaw : ∀ i j, P.map (fun ω => B ω i j) = gaussianReal 0 v)
    (s : ℝ) (hs : 1 ≤ s) :
    P.real {ω | 12 * Real.sqrt v * s * Real.sqrt n ≤
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (B ω + (B ω)ᵀ)‖} ≤ 4 * Real.exp (-(s ^ 2 * n)) :=
  opNormTail_symmetrized P n B v hv hindep
    (fun i j => hasSubgaussianMGF_of_map_gaussianReal (hlaw i j) (ne_of_gt hv)) s hs

/-- **Klartag, arXiv:2504.05042, Corollary 3.2 (p. 13), at the GOE normalisation.** If the
entries of `B` are independent `N(0, (2n)⁻¹)`, then `Γ = B + Bᵀ` is exactly the GOE of the paper
(`E Γ_ij ^ 2 = (1 + δ_ij)/n`: off-diagonal `2σ² = 1/n`, diagonal `4σ² = 2/n`), and for every
`s ≥ 1`

`P(‖Γ‖_op ≥ 6√2 · s) ≤ 4 exp (-s² n)`,

which is Klartag's `P(‖Γ‖_op ≥ C s) ≤ 4 exp (-s² n)` with the universal constant `C = 6√2`. -/
theorem goe_opNormTail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 0 < n) (B : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hindep : iIndepFun (fun (p : Fin n × Fin n) (ω : Ω) => B ω p.1 p.2) P)
    (hlaw : ∀ i j, P.map (fun ω => B ω i j) = gaussianReal 0 (2 * (n : ℝ≥0))⁻¹)
    (s : ℝ) (hs : 1 ≤ s) :
    P.real {ω | 6 * Real.sqrt 2 * s ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (B ω + (B ω)ᵀ)‖}
      ≤ 4 * Real.exp (-(s ^ 2 * n)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hn0
  have hnN : (0 : ℝ≥0) < (n : ℝ≥0) := by exact_mod_cast hn
  have hcpos : (0 : ℝ≥0) < (2 * (n : ℝ≥0))⁻¹ := by
    rw [inv_pos]; positivity
  have key := gaussian_opNormTail P n B _ hcpos hindep hlaw s hs
  have hcoe : (((2 * (n : ℝ≥0))⁻¹ : ℝ≥0) : ℝ) = (2 * (n : ℝ))⁻¹ := by push_cast; ring
  have h1 : Real.sqrt ((2 * (n : ℝ))⁻¹) * Real.sqrt (n : ℝ) = Real.sqrt 2 / 2 := by
    rw [← Real.sqrt_mul (by positivity),
      show (2 * (n : ℝ))⁻¹ * (n : ℝ) = 2⁻¹ by field_simp, Real.sqrt_inv]
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have h3 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    field_simp
    linarith
  have hthr : 12 * Real.sqrt ((((2 * (n : ℝ≥0))⁻¹ : ℝ≥0)) : ℝ) * s * Real.sqrt (n : ℝ)
      = 6 * Real.sqrt 2 * s := by
    rw [hcoe]
    calc 12 * Real.sqrt ((2 * (n : ℝ))⁻¹) * s * Real.sqrt (n : ℝ)
        = 12 * s * (Real.sqrt ((2 * (n : ℝ))⁻¹) * Real.sqrt (n : ℝ)) := by ring
      _ = 12 * s * (Real.sqrt 2 / 2) := by rw [h1]
      _ = 6 * Real.sqrt 2 * s := by ring
  rwa [hthr] at key

/-! ## Appendix. Step 3a in the unsymmetrised (`i ≤ j`) form

This is the piece report 1 §1b said the symmetrised route avoids, and estimated at ~120 lines.
It is proved here so the estimate becomes a measurement. The tail itself is *not* re-derived in
this form: the remaining work would be a mechanical duplication of `hasSubgaussianMGF_quadForm`
and `opNormTail_symmetrized` over the index type `{p : Fin n × Fin n // p.1 ≤ p.2}`, which the
brief does not require (the symmetrised form is the permitted deliverable, and the discrete chain
of hinge 1 produces a symmetrised Gaussian anyway). Note also that the unsymmetrised statement is
**not** a corollary of the symmetrised one: writing a symmetric `A` as `B + Bᵀ` forces
`B = A/2`, whose entries satisfy `B i j = B j i` and are therefore not independent over the full
product. -/

/-- A symmetric function of an ordered pair, summed over the full product, equals the sum over
`p.1 ≤ p.2` with the off-diagonal terms doubled. -/
theorem sum_prod_eq_sum_le {n : ℕ} (g : Fin n × Fin n → ℝ)
    (hg : ∀ p : Fin n × Fin n, g (Prod.swap p) = g p) :
    ∑ p : Fin n × Fin n, g p
      = ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≤ p.2),
          (if p.1 = p.2 then (1 : ℝ) else 2) * g p := by
  classical
  have hsplit1 := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Fin n × Fin n)) (fun p : Fin n × Fin n => p.1 ≤ p.2) g
  have hswap : ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => ¬ p.1 ≤ p.2), g p
      = ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2), g p := by
    refine Finset.sum_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.fst_swap, Prod.snd_swap] at ha ⊢
      exact not_le.mp ha
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.fst_swap, Prod.snd_swap] at ha ⊢
      exact not_le.mpr ha
    · intro a _; exact Prod.swap_swap a
    · intro a _; exact Prod.swap_swap a
    · intro a _; exact (hg a).symm
  have hdiag : (Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≤ p.2)).filter
      (fun p : Fin n × Fin n => p.1 = p.2)
      = Finset.univ.filter (fun p : Fin n × Fin n => p.1 = p.2) := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun p _ => ?_
    exact ⟨fun h => h.2, fun h => ⟨le_of_eq h, h⟩⟩
  have hoff : (Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≤ p.2)).filter
      (fun p : Fin n × Fin n => ¬ p.1 = p.2)
      = Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2) := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun p _ => ?_
    exact ⟨fun h => lt_of_le_of_ne h.1 h.2, fun h => ⟨le_of_lt h, ne_of_lt h⟩⟩
  have e1 : ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≤ p.2), g p
      = (∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 = p.2), g p)
        + ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2), g p := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≤ p.2))
      (fun p : Fin n × Fin n => p.1 = p.2) g, hdiag, hoff]
  have hRHS : ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≤ p.2),
      (if p.1 = p.2 then (1 : ℝ) else 2) * g p
      = (∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 = p.2), g p)
        + 2 * ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2), g p := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≤ p.2))
      (fun p : Fin n × Fin n => p.1 = p.2)
      (fun p => (if p.1 = p.2 then (1 : ℝ) else 2) * g p)]
    congr 1
    · rw [hdiag]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [Finset.mem_filter] at hp
      rw [ite_eq_left hp.2, one_mul]
    · rw [hoff, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [Finset.mem_filter] at hp
      rw [ite_eq_right (ne_of_lt hp.2)]
  rw [hRHS, ← hsplit1, e1, hswap]
  ring

/-- The quadratic form of any matrix, as a sum over the full product. -/
theorem inner_eq_sum_prod {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) A x, x⟫
      = ∑ p : Fin n × Fin n, (x p.1 * x p.2) * A p.1 p.2 := by
  rw [real_inner_comm, Matrix.inner_toEuclideanCLM, Fintype.sum_prod_type]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- **Step 3a, `i ≤ j` form.** For a symmetric matrix the quadratic form is a sum over the
subtype `{p // p.1 ≤ p.2}` — the index type on which the entries of a symmetric random matrix
are independent — with coefficients `x_i x_j` on the diagonal and `2 x_i x_j` off it. -/
theorem inner_isSymm_le {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (x : EuclideanSpace ℝ (Fin n)) :
    ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) A x, x⟫
      = ∑ p : {p : Fin n × Fin n // p.1 ≤ p.2},
          (if (p : Fin n × Fin n).1 = (p : Fin n × Fin n).2 then (1 : ℝ) else 2)
            * ((x (p : Fin n × Fin n).1 * x (p : Fin n × Fin n).2)
              * A (p : Fin n × Fin n).1 (p : Fin n × Fin n).2) := by
  classical
  have hsym : ∀ p : Fin n × Fin n,
      (fun q : Fin n × Fin n => (x q.1 * x q.2) * A q.1 q.2) (Prod.swap p)
        = (fun q : Fin n × Fin n => (x q.1 * x q.2) * A q.1 q.2) p := by
    intro p
    simp only [Prod.fst_swap, Prod.snd_swap]
    linear_combination (x p.2 * x p.1) * hA.apply p.1 p.2
  rw [inner_eq_sum_prod A x, sum_prod_eq_sum_le _ hsym]
  exact Finset.sum_subtype _ (fun q => by simp) _

end GateL10

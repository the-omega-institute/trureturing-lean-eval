import Mathlib
import Submission.L10.ChainEllipsoid

/-!
# Gate L-10 (`klartag_packing`) — H10, the lattice transfer

Brief 13, goal 1; report 7's H10; report 5 §7.2.  `ChainEllipsoid.klartag_of_chain`'s last
conjunct is `{v ∈ ellipsoid A | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0}` — an assertion about
the **integer** lattice.  The chain produces an ellipsoid free of a *different* lattice
`L = α·Λ(g)`.  The bridge is the change of basis `T` with `T(L) = ℤⁿ`.

## The observation that makes this cheap

`T = B⁻¹` where `B`'s columns are a `ℤ`-basis of `L`, and `T(E_A) = E_{BᵀAB}` — so the transfer
is a **congruence of the matrix**, and `ChainEllipsoid.quad_congr` already proves the identity
`⟪A(Bu), Bu⟫ = ⟪(BᵀAB)u, u⟫` it needs.  No `ZLattice` machinery enters `integerPoints_eq_zero`
at all; it is 20 lines.  The lattice theory is confined to `exists_basisMatrix`, which produces
`B` and, at the same time, `|det B| = ZLattice.covolume L` — the number Klartag's eq. (68) needs.

## Main results

* `mem_ellipsoid_congr` — `v ∈ E_{BᵀAB} ↔ Bv ∈ E_A`.
* `det_congr`, `congr_factor` — `det(BᵀAB) = det(B)²det(A)`, and `S' = B⁻¹S` is a congruence
  factor for `BᵀAB` whenever `S` is one for `A`.
* `integerPoints_eq_zero` — **H10**.
* `chain_hyp_of_transfer` — H10 packaged as `klartag_of_chain`'s hypothesis body.
* `exists_basisMatrix` — every full-rank `ℤ`-lattice in `Fin n → ℝ` is `B(ℤⁿ)` for an invertible
  real `B` with `|det B| = ZLattice.covolume L`.  Stated for an arbitrary lattice (rule 7);
  `ConstructionA.latR` carries the two instances, so it applies there directly.
* `chain_hyp_of_lattice` — the end-to-end statement: lattice in, `klartag_of_chain` hypothesis out,
  with the determinant condition written in terms of `ZLattice.covolume L`.
-/

open Matrix MeasureTheory Metric Set

namespace Submission.L10.LatticeTransfer

open Submission.L10.ChainEllipsoid

variable {n : ℕ}

/-- The origin is in every ellipsoid. -/
theorem zero_mem_ellipsoid (A : Matrix (Fin n) (Fin n) ℝ) :
    (0 : EuclideanSpace ℝ (Fin n)) ∈ ellipsoid A := by
  show _ < (1 : ℝ)
  simp

/-- **The congruence `A ↦ Bᵀ A B` pulls the ellipsoid back along `B`.** -/
theorem mem_ellipsoid_congr (A B : Matrix (Fin n) (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin n)) :
    v ∈ ellipsoid (Bᵀ * A * B)
      ↔ (WithLp.toLp 2 (B *ᵥ v.ofLp) : EuclideanSpace ℝ (Fin n)) ∈ ellipsoid A := by
  show _ ↔ _
  simp only [ellipsoid, Set.mem_ofPred_eq]
  rw [← quad_congr A B v.ofLp]

/-- `det (Bᵀ A B) = det(B)² det(A)`. -/
theorem det_congr (A B : Matrix (Fin n) (Fin n) ℝ) :
    (Bᵀ * A * B).det = B.det ^ 2 * A.det := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  ring

/-- The congruence factor transports: `S' = B⁻¹ S` works for `A' = Bᵀ A B`. -/
theorem congr_factor {A S B : Matrix (Fin n) (Fin n) ℝ} (hS : Sᵀ * A * S = 1)
    (hB : IsUnit B.det) :
    (B⁻¹ * S)ᵀ * (Bᵀ * A * B) * (B⁻¹ * S) = 1 := by
  have h1 : (B⁻¹)ᵀ * Bᵀ = 1 := by
    rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv B hB, Matrix.transpose_one]
  calc (B⁻¹ * S)ᵀ * (Bᵀ * A * B) * (B⁻¹ * S)
      = Sᵀ * ((B⁻¹)ᵀ * Bᵀ) * A * (B * B⁻¹) * S := by
        rw [Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
    _ = Sᵀ * A * S := by
        rw [h1, Matrix.mul_nonsing_inv B hB]
        simp [Matrix.mul_assoc]
    _ = 1 := hS

/-- **H10 — the lattice transfer.**  If `E_A` contains no non-zero point of the lattice `B(ℤⁿ)`,
then the congruent ellipsoid `E_{BᵀAB}` contains no non-zero point of `ℤⁿ`.  This is
`ChainEllipsoid.klartag_of_chain`'s last conjunct. -/
theorem integerPoints_eq_zero {A B : Matrix (Fin n) (Fin n) ℝ} (_hB : B.det ≠ 0)
    (hfree : ∀ y : Fin n → ℤ, y ≠ 0 →
      (WithLp.toLp 2 (B *ᵥ (fun i => (y i : ℝ))) : EuclideanSpace ℝ (Fin n)) ∉ ellipsoid A) :
    {v ∈ ellipsoid (Bᵀ * A * B) | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} := by
  apply Set.Subset.antisymm
  · rintro v ⟨hv, hint⟩
    choose y hy using hint
    have hvy : v.ofLp = fun i => (y i : ℝ) := by funext i; exact (hy i).symm
    by_contra hne
    rw [Set.mem_singleton_iff] at hne
    have hy0 : y ≠ 0 := by
      intro hzero
      apply hne
      apply WithLp.ofLp_injective (p := 2)
      rw [hvy, hzero]
      funext i
      simp
    exact hfree y hy0 (by
      rw [← hvy]
      exact (mem_ellipsoid_congr A B v).1 hv)
  · intro v hv
    rw [Set.mem_singleton_iff] at hv
    subst hv
    exact ⟨zero_mem_ellipsoid _, fun i => ⟨0, by simp⟩⟩

/-- **H10, packaged for `klartag_of_chain`.**  From an `L`-free ellipsoid in the lattice frame
(`L = B(ℤⁿ)`) to the hypothesis body of `ChainEllipsoid.klartag_of_chain` in the integer frame. -/
theorem chain_hyp_of_transfer {m : ℕ} {A S B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ} {c : ℝ}
    (hApos : 0 < A.det) (hS : Sᵀ * A * S = 1) (hB : B.det ≠ 0)
    (hfree : ∀ y : Fin (m + 1) → ℤ, y ≠ 0 →
      (WithLp.toLp 2 (B *ᵥ (fun i => (y i : ℝ))) : EuclideanSpace ℝ (Fin (m + 1)))
        ∉ ellipsoid A)
    (hdet : Real.sqrt (B.det ^ 2 * A.det) * (c * (m : ℝ) ^ 2)
      ≤ (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)).toReal) :
    ∃ A' S' : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ,
      0 < A'.det ∧ S'ᵀ * A' * S' = 1 ∧
      Real.sqrt A'.det * (c * (m : ℝ) ^ 2)
        ≤ (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)).toReal ∧
      {v ∈ ellipsoid A' | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} := by
  refine ⟨Bᵀ * A * B, B⁻¹ * S, ?_, congr_factor hS (isUnit_iff_ne_zero.2 hB), ?_, ?_⟩
  · rw [det_congr]
    have : 0 < B.det ^ 2 := by positivity
    exact mul_pos this hApos
  · rw [det_congr]; exact hdet
  · exact integerPoints_eq_zero hB hfree

/-! ### A basis matrix for an arbitrary `ℤ`-lattice in `ℝⁿ` -/

open Module Submodule

/-- **The basis matrix.**  Every `ℤ`-lattice of full rank in `Fin n → ℝ` is `B(ℤⁿ)` for an
invertible real matrix `B`.  Stated for an arbitrary lattice (rule 7), not for Construction A:
`Submission.L10.ConstructionA.latR` carries the two instances, so this applies to it directly. -/
theorem exists_basisMatrix (L : Submodule ℤ (Fin n → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L] :
    ∃ B : Matrix (Fin n) (Fin n) ℝ, B.det ≠ 0 ∧ |B.det| = ZLattice.covolume L ∧
      ∀ x : Fin n → ℝ, x ∈ L ↔ ∃ y : Fin n → ℤ, x = B *ᵥ (fun i => (y i : ℝ)) := by
  classical
  -- a `ℤ`-basis of `L`, reindexed by `Fin n`
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) = n := by
    have h1 : Module.finrank ℤ L = Module.finrank ℝ (Fin n → ℝ) := ZLattice.rank ℝ L
    have h2 : Module.finrank ℝ (Fin n → ℝ) = n := by simp
    have h3 := Module.finrank_eq_card_chooseBasisIndex ℤ L
    omega
  let e : Module.Free.ChooseBasisIndex ℤ L ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let b : Module.Basis (Fin n) ℤ L := (Module.Free.chooseBasis ℤ L).reindex e
  let bR : Module.Basis (Fin n) ℝ (Fin n → ℝ) := b.ofZLatticeBasis ℝ L
  have hspan : Submodule.span ℤ (Set.range (bR : Fin n → (Fin n → ℝ))) = L :=
    b.ofZLatticeBasis_span ℝ
  have hBentry : ∀ i j, ((Pi.basisFun ℝ (Fin n)).toMatrix bR) i j = bR j i := by
    intro i j
    rw [Module.Basis.toMatrix_apply, Pi.basisFun_repr]
  refine ⟨(Pi.basisFun ℝ (Fin n)).toMatrix bR, ?_, ?_, ?_⟩
  · have : Invertible ((Pi.basisFun ℝ (Fin n)).toMatrix bR) :=
      Module.Basis.invertibleToMatrix (Pi.basisFun ℝ (Fin n)) bR
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (isUnit_of_invertible _)).ne_zero
  · rw [ZLattice.covolume_eq_det L b]
    congr 1
    rw [← Matrix.det_transpose]
    congr 1
    ext i j
    rw [Matrix.transpose_apply, hBentry]
    exact congrFun (b.ofZLatticeBasis_apply ℝ L i) j
  · intro x
    have hmv : ∀ y : Fin n → ℤ,
        ((Pi.basisFun ℝ (Fin n)).toMatrix bR) *ᵥ (fun i => (y i : ℝ))
          = ∑ j : Fin n, ((y j : ℝ)) • bR j := by
      intro y
      funext i
      simp only [Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply,
        Pi.basisFun_repr, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
    rw [← hspan]
    constructor
    · intro hx
      choose y hy using (bR.mem_span_iff_repr_mem ℤ x).1 hx
      refine ⟨y, ?_⟩
      rw [hmv]
      conv_lhs => rw [← bR.sum_repr x]
      exact Finset.sum_congr rfl (fun j _ => by rw [← hy j]; rfl)
    · rintro ⟨y, rfl⟩
      rw [hmv]
      refine Submodule.sum_mem _ (fun j _ => ?_)
      have : ((y j : ℝ)) • bR j = (y j) • bR j := by
        rw [← Int.cast_smul_eq_zsmul ℝ]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j))

/-- **H10 end to end.**  A full-rank `ℤ`-lattice `L ⊆ ℝ^{m+1}`, a positive-definite `A` with a
congruence factor whose ellipsoid meets `L` only at `0`, and the determinant bound written with
`ZLattice.covolume L` — together they give the body of `ChainEllipsoid.klartag_of_chain`'s
hypothesis.  With `L = α·Λ(g)` and `covolume L = κ_n` (report 3's `covolume_latR` plus the
scaling), the determinant condition is Klartag's eq. (68). -/
theorem chain_hyp_of_lattice {m : ℕ} (L : Submodule ℤ (Fin (m + 1) → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L]
    {A S : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ} {c : ℝ}
    (hApos : 0 < A.det) (hS : Sᵀ * A * S = 1)
    (hfree : ∀ x : Fin (m + 1) → ℝ, x ∈ L → x ≠ 0 →
      (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (m + 1))) ∉ ellipsoid A)
    (hdet : ZLattice.covolume L * Real.sqrt A.det * (c * (m : ℝ) ^ 2)
      ≤ (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)).toReal) :
    ∃ A' S' : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ,
      0 < A'.det ∧ S'ᵀ * A' * S' = 1 ∧
      Real.sqrt A'.det * (c * (m : ℝ) ^ 2)
        ≤ (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)).toReal ∧
      {v ∈ ellipsoid A' | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} := by
  obtain ⟨B, hBdet, hBcov, hBmem⟩ := exists_basisMatrix L
  refine chain_hyp_of_transfer hApos hS hBdet ?_ ?_
  · intro y hy0
    refine hfree _ ((hBmem _).2 ⟨y, rfl⟩) ?_
    intro hzero
    apply hy0
    have hinv : B⁻¹ *ᵥ (B *ᵥ (fun i => (y i : ℝ))) = (fun i => (y i : ℝ)) := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul B (isUnit_iff_ne_zero.2 hBdet),
        Matrix.one_mulVec]
    rw [hzero, Matrix.mulVec_zero] at hinv
    funext i
    have := congrFun hinv.symm i
    simpa using this
  · have hsq : Real.sqrt (B.det ^ 2 * A.det) = |B.det| * Real.sqrt A.det := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs]
    rw [hsq, hBcov]
    exact hdet

end Submission.L10.LatticeTransfer

import Mathlib
import P2M.Sol.S_AlgebraicCurve_linearIndependent_of_constantFieldExtension
import Theorems.Thm_AlgebraicCurve_exists_separating_transcendental_of_perfectField
import P2M.Util
namespace P2MW.S_AlgebraicCurve_linearIndependent_of_constantFieldExtension_of_isAlgClosed

open Polynomial

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "exists_separating_transcendental_of_perfectField"
namespace LinDisjSol
p2m_open "AlgebraicCurve"

open _root_.P2MW.S_AlgebraicCurve_linearIndependent_of_constantFieldExtension.AlgebraicCurve.LinDisjSol

section FunctionField

open IntermediateField

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem exists_primitive_integral {x : F} (hx : Transcendental K x)
    [FiniteDimensional K⟮x⟯ F] [Algebra.IsSeparable K⟮x⟯ F] :
    ∃ (y : F) (m : K[X][X]) (d : ℕ), m.Monic ∧ Irreducible m ∧ m.natDegree = d ∧
      m.eval₂ (aeval x : K[X] →ₐ[K] F).toRingHom y = 0 ∧
      ∀ f : F, ∃ r : Fin d → K⟮x⟯, f = ∑ j, algebraMap K⟮x⟯ F (r j) * y ^ (j : ℕ) := by
  classical
  obtain ⟨y₀, hy₀⟩ := Field.exists_primitive_element K⟮x⟯ F
  have hy₀int : IsIntegral K⟮x⟯ y₀ := Algebra.IsIntegral.isIntegral y₀

  set μ : K⟮x⟯[X] := minpoly K⟮x⟯ y₀ with hμ
  obtain ⟨q, hq0, hq⟩ :=
    exists_common_denom hx (fun i : Fin (μ.natDegree + 1) => μ.coeff i)
  choose p hp using hq
  set s : K⟮x⟯ := aeval (AdjoinSimple.gen K x) q with hs
  have hs0 : s ≠ 0 := by
    intro h
    apply hq0
    apply aeval_gen_injective hx
    rw [map_zero]; exact h
  set y : F := algebraMap K⟮x⟯ F s * y₀ with hy
  set μs : K⟮x⟯[X] := μ.scaleRoots s with hμs
  have hμs_monic : μs.Monic := (monic_scaleRoots_iff s).mpr (minpoly.monic hy₀int)
  have hμs_root : aeval y μs = 0 := scaleRoots_aeval_eq_zero (minpoly.aeval K⟮x⟯ y₀)
  have hμs_deg : μs.natDegree = μ.natDegree := natDegree_scaleRoots _ _
  have hlifts : μs ∈ Polynomial.lifts
      (aeval (AdjoinSimple.gen K x) : K[X] →ₐ[K] K⟮x⟯).toRingHom := by
    rw [lifts_iff_coeff_lifts]
    intro n
    rw [hμs, coeff_scaleRoots]
    rcases lt_trichotomy n μ.natDegree with hlt | heq | hgt
    · obtain ⟨k, hk⟩ : ∃ k, μ.natDegree - n = k + 1 := ⟨μ.natDegree - n - 1, by omega⟩
      refine ⟨p ⟨n, by omega⟩ * q ^ k, ?_⟩
      have := hp ⟨n, by omega⟩
      simp only at this
      change aeval (AdjoinSimple.gen K x) (p ⟨n, by omega⟩ * q ^ k) = _
      rw [map_mul, map_pow, ← this, hk, pow_succ]
      ring
    · subst heq
      refine ⟨1, ?_⟩
      change aeval (AdjoinSimple.gen K x) (1 : K[X]) = _
      rw [map_one, Nat.sub_self, pow_zero, mul_one]
      exact (minpoly.monic hy₀int).coeff_natDegree.symm
    · refine ⟨0, ?_⟩
      change aeval (AdjoinSimple.gen K x) (0 : K[X]) = _
      rw [map_zero, coeff_eq_zero_of_natDegree_lt hgt, zero_mul]
  obtain ⟨m, hmμs, hmdeg, hmmonic⟩ := lifts_and_natDegree_eq_and_monic hlifts hμs_monic

  have hyint : IsIntegral K⟮x⟯ y := Algebra.IsIntegral.isIntegral y
  have htop : K⟮x⟯⟮y⟯ = ⊤ := by
    rw [eq_top_iff, ← hy₀, adjoin_simple_le_iff]
    have : y₀ = algebraMap K⟮x⟯ F s⁻¹ * y := by
      rw [hy, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hs0, map_one, one_mul]
    rw [this]
    exact mul_mem (IntermediateField.algebraMap_mem _ _) (mem_adjoin_simple_self _ y)
  have hdegμ : μ.natDegree = Module.finrank K⟮x⟯ F := by
    rw [hμ, ← adjoin.finrank hy₀int, hy₀, finrank_top']
  have hdegy : (minpoly K⟮x⟯ y).natDegree = Module.finrank K⟮x⟯ F := by
    rw [← adjoin.finrank hyint, htop, finrank_top']
  have hμs_eq : μs = minpoly K⟮x⟯ y :=
    eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hyint) hμs_monic
      (minpoly.dvd _ _ hμs_root) (by rw [hμs_deg, hdegμ, hdegy])
  have hirr : Irreducible m :=
    Monic.irreducible_of_irreducible_map _ m hmmonic
      (by rw [hmμs, hμs_eq]; exact minpoly.irreducible hyint)
  have hroot : m.eval₂ (aeval x : K[X] →ₐ[K] F).toRingHom y = 0 := by
    have h := hμs_root
    rw [← hmμs, aeval_def, eval₂_map] at h
    rwa [← algebraMap_comp_aeval_gen x]

  let pb := adjoin.powerBasis hyint
  refine ⟨y, m, (minpoly K⟮x⟯ y).natDegree, hmmonic, hirr, ?_, hroot, fun f => ?_⟩
  · rw [hmdeg, hμs_eq]
  · have hf : f ∈ K⟮x⟯⟮y⟯ := by rw [htop]; exact mem_top
    refine ⟨fun j => pb.basis.repr ⟨f, hf⟩ j, ?_⟩
    have hsum := pb.basis.sum_repr ⟨f, hf⟩
    calc f = (K⟮x⟯⟮y⟯).val ⟨f, hf⟩ := rfl
      _ = (K⟮x⟯⟮y⟯).val (∑ i, pb.basis.repr ⟨f, hf⟩ i • pb.basis i) := by rw [hsum]
      _ = _ := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, Algebra.smul_def, pb.basis_eq_pow, map_pow]
        rfl

end FunctionField

section Main

open IntermediateField

variable {K F K' F' : Type*} [Field K] [Field F] [Field K'] [Field F'] [Algebra K F]
  [Algebra K' F'] [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F']
  [IsScalarTower K F F']

theorem eq_zero_of_sum_mul_algebraMap [IsAlgClosed K] {x : F}
    (hx : Transcendental K x) [FiniteDimensional K⟮x⟯ F] [Algebra.IsSeparable K⟮x⟯ F]
    (hx₁ : Transcendental K' (algebraMap F F' x))
    {κ : Type*} [Fintype κ] {c : κ → K'} (hc : LinearIndependent K c) (f : κ → F)
    (hrel : ∑ k, algebraMap F F' (f k) * algebraMap K' F' (c k) = 0) : ∀ k, f k = 0 := by
  classical
  obtain ⟨y, m, d, hm, hirr, hd, hroot, hspan⟩ := exists_primitive_integral hx
  subst hd
  obtain ⟨ρ, hρ⟩ := exists_ringHom_adjoin (K := K) (K' := K') (F' := F') x
  have hLD := linearIndependent_pow_algebraMap (K := K) hx₁ hm hirr hroot
  choose r hr using fun k => hspan (f k)
  obtain ⟨q, hq0, hq⟩ := exists_common_denom hx (fun kj : κ × Fin m.natDegree => r kj.1 kj.2)
  choose P hP using hq

  have hcoefE : ∀ j : Fin m.natDegree,
      ∑ k, algebraMap K' K'⟮algebraMap F F' x⟯ (c k) * ρ (r k j) = 0 := by
    have hsum : ∑ j : Fin m.natDegree,
        (∑ k, algebraMap K' K'⟮algebraMap F F' x⟯ (c k) * ρ (r k j)) •
          algebraMap F F' y ^ (j : ℕ) = 0 := by
      rw [← hrel]
      simp_rw [Finset.sum_smul, Algebra.smul_def]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hr k, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, map_mul, ← IsScalarTower.algebraMap_apply, hρ, map_pow]
      ring
    exact Fintype.linearIndependent_iff.mp hLD _ hsum

  have hρθ : ∀ p : K[X], ρ (aeval (AdjoinSimple.gen K x) p) =
      aeval (AdjoinSimple.gen K' (algebraMap F F' x)) (p.map (algebraMap K K')) := by
    intro p
    apply (algebraMap K'⟮algebraMap F F' x⟯ F').injective
    rw [hρ]
    change algebraMap F F' ((aeval (AdjoinSimple.gen K x) p : K⟮x⟯) : F) =
      ((aeval (AdjoinSimple.gen K' (algebraMap F F' x)) (p.map (algebraMap K K')) :
        K'⟮algebraMap F F' x⟯) : F')
    rw [AdjoinSimple.coe_aeval_gen_apply, AdjoinSimple.coe_aeval_gen_apply, aeval_map_algebraMap,
      aeval_algebraMap_apply]
  have hP0 : ∀ k j, P (k, j) = 0 := by
    intro k j
    refine eq_zero_of_sum_aeval hx₁ hc (fun k => P (k, j)) ?_ k
    have := congrArg (fun z => ρ (aeval (AdjoinSimple.gen K x) q) * z) (hcoefE j)
    simp only [mul_zero, Finset.mul_sum] at this
    rw [← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hρθ, ← hP (k, j), map_mul]
    ring

  have hs0 : (aeval (AdjoinSimple.gen K x) q : K⟮x⟯) ≠ 0 := by
    intro h
    apply hq0
    apply aeval_gen_injective hx
    rw [map_zero]; exact h
  have hr0 : ∀ k j, r k j = 0 := by
    intro k j
    have := hP (k, j)
    rw [hP0 k j, map_zero] at this
    exact (mul_eq_zero.mp this).resolve_left hs0
  intro k
  rw [hr k]
  simp [hr0]

theorem linearIndependent_algebraMap_of_fintype [IsAlgClosed K] {x : F}
    (hx : Transcendental K x) [FiniteDimensional K⟮x⟯ F] [Algebra.IsSeparable K⟮x⟯ F]
    (hx₁ : Transcendental K' (algebraMap F F' x))
    {κ : Type*} [Fintype κ] {b : κ → F} (hb : LinearIndependent K b) :
    LinearIndependent K' (fun i => algebraMap F F' (b i)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a hrel i₀
  let W : Submodule K K' := Submodule.span K (Set.range a)
  haveI : Module.Finite K W := Module.Finite.span_of_finite K (Set.finite_range a)
  let bW := Module.finBasis K W
  let c : Fin (Module.finrank K W) → K' := fun k => (bW k : K')
  have hc : LinearIndependent K c :=
    bW.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  have ha : ∀ i, a i ∈ W := fun i => Submodule.subset_span ⟨i, rfl⟩
  let μ : κ → Fin (Module.finrank K W) → K := fun i k => bW.repr ⟨a i, ha i⟩ k
  have hai : ∀ i, a i = ∑ k, μ i k • c k := by
    intro i
    have h1 := congrArg (Submodule.subtype W) (bW.sum_repr ⟨a i, ha i⟩)
    rw [map_sum] at h1
    simp only [map_smul, Submodule.subtype_apply] at h1
    exact h1.symm
  let f : Fin (Module.finrank K W) → F := fun k => ∑ i, μ i k • b i
  have hf : ∀ k, f k = 0 := by
    apply eq_zero_of_sum_mul_algebraMap hx hx₁ hc f
    have lhs : ∑ k, algebraMap F F' (f k) * algebraMap K' F' (c k) =
        ∑ k, ∑ i, algebraMap K F' (μ i k) * algebraMap F F' (b i) * algebraMap K' F' (c k) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [f, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]
    have rhs : ∑ i, a i • algebraMap F F' (b i) =
        ∑ i, ∑ k, algebraMap K F' (μ i k) * algebraMap F F' (b i) * algebraMap K' F' (c k) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hai i, Algebra.smul_def, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]
      ring
    rw [lhs, Finset.sum_comm, ← rhs, hrel]
  have hμ : ∀ k i, μ i k = 0 := fun k =>
    Fintype.linearIndependent_iff.mp hb (fun i => μ i k) (hf k)
  rw [hai i₀]
  simp [hμ]

end Main

end AlgebraicCurve.LinDisjSol

open AlgebraicCurve.LinDisjSol in

theorem solution (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    {ι : Type*} {b : ι → F} (hb : LinearIndependent K b) :
    LinearIndependent K' (fun i => algebraMap F F' (b i)) := by
  obtain ⟨x₀, hx₀, hfin₀⟩ := hfg

  obtain ⟨x, hx, hfin, hsep⟩ :=
    AlgebraicCurve.exists_separating_transcendental_of_perfectField hx₀ hfin₀
  haveI := hfin
  haveI := hsep
  have hx₁ : Transcendental K' (algebraMap F F' x) :=
    transcendental_algebraMap (K := K) (x := x) hfg' hgen
  rw [linearIndependent_iff_finset_linearIndependent]
  intro s
  exact linearIndependent_algebraMap_of_fintype hx hx₁ (hb.comp ((↑) : s → ι) Subtype.val_injective)

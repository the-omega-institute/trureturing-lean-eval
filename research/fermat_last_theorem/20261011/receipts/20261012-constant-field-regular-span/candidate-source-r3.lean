import Mathlib
import P2M.Sol.S_AlgebraicCurve_mem_span_range_algebraMap_of_constantFieldExtension
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_ringHom_of_isSeparable
import Theorems.Thm_AlgebraicCurve_exists_separating_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_Place_mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_linearIndependent_of_constantFieldExtension_of_isAlgClosed
import P2M.Util
namespace P2MW.S_AlgebraicCurve_mem_span_range_algebraMap_of_constantFieldExtension_of_isAlgClosed
attribute [-instance] AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_mem_span_range_algebraMap_of_constantFieldExtension_of_isAlgClosed.AlgebraicCurve Polynomial"

open _root_.P2MW.S_AlgebraicCurve_mem_span_range_algebraMap_of_constantFieldExtension.AlgebraicCurve.W7XH

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord Place.ord_zero Divisor Divisor.degree HasPrincipalDivisors HasPrincipalDivisors.exists_divisor IsCurveOver IsCurveOver.deg_eq_one_of_isAlgClosed IsCurveOver.finiteResidue Place.exists_comap_algebraMap_eq_of_constantFieldExtension_of_isAlgClosed Place.exists_toValuationSubring_eq_comap_ringHom_of_isSeparable exists_separating_transcendental_of_perfectField Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed linearIndependent_of_constantFieldExtension_of_isAlgClosed"
namespace W7XH
p2m_open "AlgebraicCurve"

section CFE

variable {K F K' F' : Type*} [Field K] [Field F] [Field K'] [Field F'] [Algebra K F]
  [Algebra K' F'] [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F']
  [IsScalarTower K F F']

theorem transcendental_algebraMap [IsAlgClosed K] [IsAlgClosed K']
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K F]
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    {x : F} (hx : Transcendental K x) :
    Transcendental K' (algebraMap F F' x) := by
  obtain ⟨j, hj, hfin⟩ := id hfg
  have := hfin
  obtain ⟨v, hv⟩ : ∃ v : Place K F, v.ord x ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨a, ha⟩ := Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed j hj h
    exact hx (ha ▸ isAlgebraic_algebraMap a)
  obtain ⟨P', -, hord, -⟩ :=
    Place.exists_comap_algebraMap_eq_of_constantFieldExtension_of_isAlgClosed K F K' F' hfg hfg' hgen v
  intro halg
  obtain ⟨a, ha⟩ := mem_range_of_isAlgebraic halg
  have h1 := hord x
  rw [← ha, ord_algebraMap] at h1
  exact hv h1.symm

theorem algebraMap_mem_of_new (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F]
    (W : Place K' F')
    (hW : ∀ v : Place K F, W.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring)
    (f : F) : algebraMap F F' f ∈ W.toValuationSubring := by
  by_contra hf
  set A := W.toValuationSubring.comap (algebraMap F F') with hA
  have hAK : ∀ a : K, algebraMap K F a ∈ A := fun a => by
    rw [hA, ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply K K' F']
    exact W.algebraMap_mem' _
  have hAtop : A ≠ ⊤ := by
    intro h
    apply hf
    have : f ∈ A := h ▸ Subring.mem_top f
    exact (ValuationSubring.mem_comap).1 this
  have hfA : f ∉ A := fun h => hf ((ValuationSubring.mem_comap).mp (hA ▸ h))
  obtain ⟨v, hv₀⟩ := Place.exists_toValuationSubring_eq_comap_ringHom_of_isSeparable
      (K := K) x (RingHom.id F) A hAK ⟨f, hfA⟩
  have hv : v.toValuationSubring = A := by
    rw [hv₀]; ext g; simp [ValuationSubring.mem_comap]
  exact hW v hv.symm

theorem trace_mem [IsAlgClosed K] [IsAlgClosed K'] [IsCurveOver K F] [IsCurveOver K' F']
    {x : F} (hx : Transcendental K x)
    (hfg' : ∃ j : F', Transcendental K' j ∧
      FiniteDimensional (IntermediateField.adjoin K' ({j} : Set F')) F')
    [FiniteDimensional (IntermediateField.adjoin K' ({algebraMap F F' x} : Set F')) F']
    {c : K'} (hc : c ∉ Set.range (algebraMap K K'))
    (v' : Place K' F') (hv' : 0 < v'.ord (algebraMap F F' x - algebraMap K' F' c))
    (w : F')
    (hw : ∀ W : Place K' F',
      (∀ v : Place K F, W.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring) →
        w ∈ W.toValuationSubring) :
    ((Algebra.trace (IntermediateField.adjoin K' ({algebraMap F F' x} : Set F')) F' w :
      IntermediateField.adjoin K' ({algebraMap F F' x} : Set F')) : F') ∈ v'.toValuationSubring := by
  set x' := algebraMap F F' x with hx'
  set kx' : IntermediateField K' F' := IntermediateField.adjoin K' ({x'} : Set F') with hkx'
  set R : ValuationSubring kx' := v'.toValuationSubring.comap (algebraMap kx' F') with hR
  have hRmem : ∀ g : kx', g ∈ R ↔ (g : F') ∈ v'.toValuationSubring := fun g =>
    ValuationSubring.mem_comap
  have hx'c_mem : x' - algebraMap K' F' c ∈ v'.toValuationSubring := mem_of_ord_nonneg v' hv'.le
  have hx'v' : x' ∈ v'.toValuationSubring := by
    have := add_mem hx'c_mem (v'.algebraMap_mem' c)
    simpa using this
  have hx'k : x' ∈ kx' := IntermediateField.mem_adjoin_simple_self K' x'

  have hnew : ∀ W : Place K' F',
      (∀ g : F', g ∈ kx' → g ∈ v'.toValuationSubring → g ∈ W.toValuationSubring) →
      ∀ v : Place K F, W.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring := by
    intro W hmemW v heq
    have hcomap : ∀ f : F, f ∈ v.toValuationSubring ↔ algebraMap F F' f ∈ W.toValuationSubring := by
      intro f
      rw [← heq, ValuationSubring.mem_comap]
    have hxv : x ∈ v.toValuationSubring := (hcomap x).2 (hmemW x' hx'k hx'v')
    obtain ⟨a, ha⟩ := exists_ord_sub_algebraMap_pos v hxv
    rcases ha with ha | ha
    · exact hx (ha ▸ isAlgebraic_algebraMap a)
    set u := x - algebraMap K F a with hu
    have hui : u⁻¹ ∉ v.toValuationSubring := not_mem_of_ord_neg v (by rw [v.ord_inv]; omega)
    apply hui
    rw [hcomap, map_inv₀]
    have hφu : algebraMap F F' u = x' - algebraMap K' F' (algebraMap K K' a) := by
      rw [hu, map_sub, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    have hca : c - algebraMap K K' a ≠ 0 := by
      intro h
      exact hc ⟨a, (sub_eq_zero.mp h).symm⟩
    have hord0 : v'.ord (algebraMap F F' u) = 0 := by
      rw [hφu]
      have : x' - algebraMap K' F' (algebraMap K K' a) =
          algebraMap K' F' (c - algebraMap K K' a) + (x' - algebraMap K' F' c) := by
        rw [map_sub]; ring
      rw [this]
      exact ord_algebraMap_add_eq_zero v' hca hv'
    apply hmemW
    · rw [hφu]
      exact inv_mem (sub_mem hx'k (kx'.algebraMap_mem _))
    · apply mem_of_ord_nonneg
      rw [v'.ord_inv, hord0, neg_zero]

  have hint : IsIntegral R w := by
    apply isIntegral_of_forall_mem_valuationSubring
    intro B hB
    have hB' : ∀ g : F', g ∈ kx' → g ∈ v'.toValuationSubring → g ∈ B := by
      intro g hg1 hg2
      exact hB ⟨⟨g, hg1⟩, (hRmem _).2 hg2⟩
    by_contra hwB
    have hBtop : B ≠ ⊤ := fun h => hwB (h ▸ Subring.mem_top w)
    have hBK : ∀ a : K', algebraMap K' F' a ∈ B := fun a =>
      hB' _ (kx'.algebraMap_mem a) (v'.algebraMap_mem' a)
    obtain ⟨j₀, hj₀, hfin₀⟩ := id hfg'
    obtain ⟨j, _hj, hfin, hsep_j⟩ :=
      AlgebraicCurve.exists_separating_transcendental_of_perfectField hj₀ hfin₀
    have := hfin; have := hsep_j
    obtain ⟨W, hW₀⟩ :=
      Place.exists_toValuationSubring_eq_comap_ringHom_of_isSeparable
        (K := K') j (RingHom.id F') B (by simpa using hBK) ⟨w, by simpa using hwB⟩
    have hW : W.toValuationSubring = B := by
      rw [hW₀]; ext g; simp [ValuationSubring.mem_comap]
    have hWnew := hnew W (fun g hg1 hg2 => by rw [hW]; exact hB' g hg1 hg2)
    exact hwB (hW ▸ hw W hWnew)
  have htr : IsIntegral R (Algebra.trace kx' F' w) := Algebra.isIntegral_trace hint
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := R) (K := kx')).mp htr
  have hmem : Algebra.trace kx' F' w ∈ R := hy ▸ y.2
  exact (hRmem _).1 hmem

end CFE

section BaseChange

variable {K F K' F' : Type*} [Field K] [Field F] [Field K'] [Field F'] [Algebra K F]
  [Algebra K' F'] [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F']
  [IsScalarTower K F F']

theorem exists_basis [IsAlgClosed K] [IsAlgClosed K']
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K F]
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    {x : F} (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    {n : ℕ} (y : Module.Basis (Fin n) (IntermediateField.adjoin K ({x} : Set F)) F) :
    ∃ y' : Module.Basis (Fin n) (IntermediateField.adjoin K' ({algebraMap F F' x} : Set F')) F',
      ∀ i, y' i = algebraMap F F' (y i) := by
  classical
  let kx : IntermediateField K F := IntermediateField.adjoin K ({x} : Set F)
  set x' := algebraMap F F' x with hx'def
  set kx' : IntermediateField K' F' := IntermediateField.adjoin K' ({x'} : Set F') with hkx'
  have hx' : Transcendental K' x' := transcendental_algebraMap hfg hfg' hgen hx

  have hli : LinearIndependent kx' (fun i => algebraMap F F' (y i)) := by
    rw [linearIndependent_iff']
    intro s r hr i hi
    have hden : ∀ i, ∃ b : K'[X], aeval x' b ≠ 0 ∧
        ∃ P : K'[X], aeval x' b * (r i : F') = aeval x' P := by
      intro i
      have hri : (r i : F') ∈ IntermediateField.adjoin K' ({x'} : Set F') := (r i).2
      rw [IntermediateField.mem_adjoin_simple_iff] at hri
      obtain ⟨P, b, hPb⟩ := hri
      by_cases hb : aeval x' b = 0
      · refine ⟨1, by simp, 0, ?_⟩
        rw [hPb, hb, div_zero]
        simp
      · exact ⟨b, hb, P, by rw [hPb, mul_div_cancel₀ _ hb]⟩
    choose b hb P hP using hden
    set B := ∏ j, aeval x' (b j) with hB
    have hB0 : B ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => hb j
    set Q : Fin n → K'[X] := fun i => (∏ j ∈ Finset.univ.erase i, b j) * P i with hQ
    have hBQ : ∀ i, B * (r i : F') = aeval x' (Q i) := by
      intro i
      simp only [hQ]
      rw [map_mul, map_prod, ← hP i, ← mul_assoc, hB,
        Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    set N := (Finset.univ.sup fun i => (Q i).natDegree) + 1 with hN
    have hQN : ∀ i, (Q i).natDegree < N := fun i =>
      Nat.lt_succ_of_le (Finset.le_sup (f := fun i => (Q i).natDegree) (Finset.mem_univ i))
    have hrel : ∑ p ∈ Finset.range N ×ˢ s,
        algebraMap K' F' ((Q p.2).coeff p.1) * algebraMap F F' (x ^ p.1 * y p.2) = 0 := by
      have h0 : ∑ i ∈ s, (r i : F') * algebraMap F F' (y i) = 0 := by
        simpa [Algebra.smul_def] using hr
      have h1 : ∑ i ∈ s, aeval x' (Q i) * algebraMap F F' (y i) = 0 := by
        have : ∑ i ∈ s, aeval x' (Q i) * algebraMap F F' (y i) =
            B * ∑ i ∈ s, (r i : F') * algebraMap F F' (y i) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← hBQ, mul_assoc]
        rw [this, h0, mul_zero]
      rw [Finset.sum_product_right, ← h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [aeval_def, eval₂_eq_sum_range' _ (hQN i), Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_mul, map_pow]
      ring
    have hKind : LinearIndependent K (fun p : ℕ × Fin n => x ^ p.1 * y p.2) := by
      have hxk : Transcendental K (⟨x, IntermediateField.mem_adjoin_simple_self K x⟩ : kx) := by
        rw [← transcendental_algebraMap_iff (FaithfulSMul.algebraMap_injective kx F)]
        exact hx
      have h1 := linearIndependent_pow_of_transcendental hxk
      have h2 := linearIndependent_smul h1 y.linearIndependent
      convert h2 using 1 <;> first | rfl | (funext p; simp [Algebra.smul_def])
    have hK'ind := AlgebraicCurve.linearIndependent_of_constantFieldExtension_of_isAlgClosed
      K F K' F' hfg hfg' hgen hKind
    have hrel' : ∑ p ∈ Finset.range N ×ˢ s,
        (Q p.2).coeff p.1 • algebraMap F F' (x ^ p.1 * y p.2) = 0 := by
      simpa only [Algebra.smul_def] using hrel
    have hcoeff := (linearIndependent_iff'.1 hK'ind) _ _ hrel'
    have hQi : Q i = 0 := by
      ext a
      rw [coeff_zero]
      by_cases ha : a < N
      · exact hcoeff (a, i) (Finset.mk_mem_product (Finset.mem_range.2 ha) hi)
      · exact coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hQN i) (not_lt.1 ha))
    have h1 : B * (r i : F') = 0 := by rw [hBQ, hQi, map_zero]
    have h2 : (r i : F') = 0 := (mul_eq_zero.1 h1).resolve_left hB0
    exact_mod_cast h2

  have hsp : ⊤ ≤ Submodule.span kx' (Set.range fun i => algebraMap F F' (y i)) := by
    have hφ : ∀ f : F, algebraMap F F' f ∈
        Submodule.span kx' (Set.range fun i => algebraMap F F' (y i)) := by
      intro f
      rw [← y.sum_repr f, map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [algebraMap_smul (K' := K') (F' := F')]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have : Algebra.IsIntegral kx F := Algebra.IsIntegral.of_finite kx F
    have halg : ∀ g ∈ Set.range (algebraMap F F'), IsAlgebraic kx' g := by
      rintro _ ⟨f, rfl⟩
      have hint : IsIntegral kx f := Algebra.IsIntegral.isIntegral f
      have : IsIntegral kx' (algebraMap F F' f) := by
        refine ⟨(minpoly kx f).map (iota K K' F' x), (minpoly.monic hint).map _, ?_⟩
        rw [eval₂_map]
        have hcomp : (algebraMap kx' F').comp (iota K K' F' x) =
            (algebraMap F F').comp (algebraMap kx F) := by
          ext a
          rfl
        rw [hcomp, ← hom_eval₂, ← aeval_def, minpoly.aeval, map_zero]
      exact this.isAlgebraic
    have hmem : ∀ z : F', z ∈ Submodule.span kx' (Set.range (algebraMap F F')) := by
      intro z
      set E : IntermediateField kx' F' := IntermediateField.adjoin kx' (Set.range (algebraMap F F'))
        with hE
      have hzE : z ∈ E := by
        have hle : IntermediateField.adjoin K' (Set.range (algebraMap F F')) ≤
            IntermediateField.restrictScalars K' E :=
          IntermediateField.adjoin_le_iff.mpr (IntermediateField.subset_adjoin _ _)
        have := hle (hgen ▸ IntermediateField.mem_top (x := z))
        exact (IntermediateField.mem_restrictScalars K').1 this
      have hzA : z ∈ Algebra.adjoin kx' (Set.range (algebraMap F F')) := by
        rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg]
        exact hzE
      have : z ∈ Subalgebra.toSubmodule (Algebra.adjoin kx' (Set.range (algebraMap F F'))) := hzA
      rwa [span_range_eq_adjoin] at this
    intro z _
    have := hmem z
    refine (Submodule.span_le.2 ?_) this
    rintro _ ⟨f, rfl⟩
    exact hφ f
  exact ⟨Module.Basis.mk hli hsp, fun i => by rw [Module.Basis.mk_apply]⟩

end BaseChange

section Main

theorem mem_span_range_algebraMap_of_constantFieldExtension
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [IsAlgClosed K']
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K F] [IsCurveOver K' F']
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (z : F')
    (hz : ∀ v' : Place K' F',
      (∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring) →
        z ∈ v'.toValuationSubring) :
    z ∈ Submodule.span K' (Set.range (algebraMap F F')) := by
  classical

  obtain ⟨x₀, hx₀, hfin₀⟩ := id hfg
  obtain ⟨x, hx, hfin, hsep_kx⟩ :=
    AlgebraicCurve.exists_separating_transcendental_of_perfectField hx₀ hfin₀
  have := hfin
  set kx : IntermediateField K F := IntermediateField.adjoin K ({x} : Set F) with hkx
  set x' := algebraMap F F' x with hx'def
  set kx' : IntermediateField K' F' := IntermediateField.adjoin K' ({x'} : Set F') with hkx'
  have : Algebra.IsSeparable kx F := hsep_kx
  have hx' : Transcendental K' x' := transcendental_algebraMap hfg hfg' hgen hx
  let y : Module.Basis (Fin (Module.finrank kx F)) kx F := Module.finBasis kx F
  obtain ⟨y', hy⟩ := exists_basis hfg hfg' hgen hx y
  have : FiniteDimensional kx' F' := Module.Finite.of_basis y'
  set yd := (Algebra.traceForm kx F).dualBasis (traceForm_nondegenerate kx F) y with hyd
  have ht : ∀ i, ((Algebra.trace kx' F' (z * algebraMap F F' (yd i)) : kx') : F') ∈
      Submodule.span K' (Set.range (algebraMap F F')) := by
    intro i
    refine mem_span_of_regular (K := K) hfg' hx' (Subtype.mem _) ?_
    intro c hc v' hv'
    apply ord_nonneg_of_mem
    apply trace_mem hx hfg' hc v' hv'
    intro W hW
    exact mul_mem (hz W hW) (algebraMap_mem_of_new x W hW _)
  have hA : ∀ t, t ∈ Submodule.span K' (Set.range (algebraMap F F')) → ∀ f : F,
      t * algebraMap F F' f ∈ Submodule.span K' (Set.range (algebraMap F F')) := by
    intro t ht f
    rw [← span_range_eq_adjoin] at ht ⊢
    exact (Algebra.adjoin K' _).mul_mem ht (Algebra.subset_adjoin ⟨f, rfl⟩)
  rw [eq_sum_trace_mul y y' hy z]
  exact Submodule.sum_mem _ fun i _ => hA _ (ht i) _

end Main

end AlgebraicCurve.W7XH
p2m_reactivate "P2MW.S_AlgebraicCurve_mem_span_range_algebraMap_of_constantFieldExtension_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_mem_span_range_algebraMap_of_constantFieldExtension_of_isAlgClosed.AlgebraicCurve.W7XH"
p2m_reactivate "P2MW.S_AlgebraicCurve_mem_span_range_algebraMap_of_constantFieldExtension_of_isAlgClosed.AlgebraicCurve"

theorem solution
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [IsAlgClosed K']
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K F] [IsCurveOver K' F']
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (z : F')
    (hz : ∀ v' : Place K' F',
      (∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring) →
        z ∈ v'.toValuationSubring) :
    z ∈ Submodule.span K' (Set.range (algebraMap F F')) :=
  AlgebraicCurve.W7XH.mem_span_range_algebraMap_of_constantFieldExtension K F K' F' hfg hfg' hgen z hz

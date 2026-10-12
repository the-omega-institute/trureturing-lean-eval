import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_AlgebraicCurve_mem_span_range_algebraMap_of_constantFieldExtension_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_mem_riemannRochSpace_of_sum_basis_smul_algebraMap_mem_mapDomain
import Theorems.Thm_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_ringHom_of_isSeparable
import Theorems.Thm_AlgebraicCurve_exists_separating_transcendental_of_perfectField
import P2M.Util
import Submission.Supplier.P2M.Sol.S_AlgebraicCurve_Place_ordDifferential_D_eq_zero_of_constantFieldExtension_of_forall_mem
namespace P2MW.S_AlgebraicCurve_lSpace_mapDomain_subset_span_image_lSpace_of_constantFieldExtension_of_isAlgClosed
attribute [-instance] AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut
attribute [-simp] AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq
attribute [-simp] WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply

set_option autoImplicit false
set_option maxHeartbeats 4000000

open AlgebraicCurve

open P2MW.S_AlgebraicCurve_Place_ordDifferential_D_eq_zero_of_constantFieldExtension_of_forall_mem.W7XNewPlaces

theorem solution
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [IsAlgClosed K'] [IsCurveOver K F] [IsCurveOver K' F']
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (lift : Place K F → Place K' F')
    (hlift_ord : ∀ (P : Place K F) (f : F), (lift P).ord (algebraMap F F' f) = P.ord f)
    (hlift_inj : Function.Injective lift)
    (_hlift_new : ∀ v' : Place K' F', (∀ v, lift v ≠ v') →
      ∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring)
    (D : Divisor K F) {f' : F'}
    (hf' : f' ∈ LSpace (K := K') (Finsupp.mapDomain lift D)) :
    f' ∈ Submodule.span K' ((algebraMap F F') '' (LSpace (K := K) D : Set F)) := by
  classical

  have hnew : ∀ v' : Place K' F', (∀ v : Place K F,
      v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring) →
      f' ∈ v'.toValuationSubring := by
    intro v' hv'
    have hnr : ∀ v, lift v ≠ v' := fun v hev => hv' v (by
      rw [← hev]; ext g
      rw [ValuationSubring.mem_comap, mem_iff_ord_nonneg, mem_iff_ord_nonneg, hlift_ord])
    have hD0 : (Finsupp.mapDomain lift D) v' = 0 :=
      Finsupp.mapDomain_of_notMem_range D v' (by simpa [Set.range] using hnr)
    rcases mem_lSpace_iff_ord.mp hf' with rfl | hord
    · exact zero_mem _
    · rw [mem_iff_ord_nonneg]; have := hord v'; rw [hD0, neg_zero] at this; exact this
  have hspan' : f' ∈ Submodule.span K' (Set.range (algebraMap F F')) :=
    mem_span_range_algebraMap_of_constantFieldExtension_of_isAlgClosed
      K F K' F' hfg hfg' hgen f' hnew

  let B := Module.Basis.ofVectorSpace K K'
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hspan'

  let g : Module.Basis.ofVectorSpaceIndex K K' →₀ F :=
    (Finsupp.ofSupportFinite
      (fun j => ∑ f ∈ c.support, (B.repr (c f) j) • f)
      ((c.support.finite_toSet.biUnion fun f _ => (B.repr (c f)).support.finite_toSet).subset
        (fun j hj => by
          simp only [Function.mem_support, ne_eq] at hj
          simp only [Set.mem_iUnion, Finset.mem_coe, Finsupp.mem_support_iff, ne_eq]
          by_contra h; push Not at h
          exact hj (Finset.sum_eq_zero fun f hf => by
            rw [h f (Finsupp.mem_support_iff.mp hf), zero_smul]))))
  have hf'eq : f' = ∑ j ∈ g.support, algebraMap K' F' (B j) * algebraMap F F' (g j) := by
    have hgj : ∀ j, (g j : F) = ∑ f ∈ c.support, B.repr (c f) j • f := fun _ => rfl
    let S : Finset _ := c.support.biUnion fun f => (B.repr (c f)).support
    have hgsub : g.support ⊆ S := by
      intro j hj
      rw [Finsupp.mem_support_iff, hgj] at hj
      simp only [S, Finset.mem_biUnion, Finsupp.mem_support_iff]
      by_contra h; push Not at h
      exact hj (Finset.sum_eq_zero fun f hf => by
        rw [h f (Finsupp.mem_support_iff.mp hf), zero_smul])
    have hcf_S : ∀ f ∈ c.support, c f = ∑ j ∈ S, B.repr (c f) j • B j := by
      intro f hf
      conv_lhs => rw [← B.linearCombination_repr (c f), Finsupp.linearCombination_apply,
        Finsupp.sum]
      refine Finset.sum_subset ?_ fun j _ hj => by
        rw [Finsupp.notMem_support_iff.mp hj, zero_smul]
      exact Finset.subset_biUnion_of_mem (fun f => (B.repr (c f)).support) hf
    have hterm : ∀ (j : Module.Basis.ofVectorSpaceIndex K K') (f : F),
        algebraMap K' F' (B.repr (c f) j • B j) * algebraMap F F' f =
        algebraMap K' F' (B j) * algebraMap F F' (B.repr (c f) j • f) := by
      intro j f
      rw [Algebra.smul_def (R := K) (A := K'), map_mul,
        Algebra.smul_def (R := K) (A := F), map_mul,
        ← IsScalarTower.algebraMap_apply K K' F',
        ← IsScalarTower.algebraMap_apply K F F']
      ring
    calc f' = ∑ f ∈ c.support, c f • algebraMap F F' f := by
          rw [← hc]; rfl
      _ = ∑ f ∈ c.support, ∑ j ∈ S,
            algebraMap K' F' (B.repr (c f) j • B j) * algebraMap F F' f := by
          refine Finset.sum_congr rfl fun f hf => ?_
          conv_lhs => rw [Algebra.smul_def, hcf_S f hf]
          rw [map_sum, Finset.sum_mul]
      _ = ∑ j ∈ S, ∑ f ∈ c.support,
            algebraMap K' F' (B j) * algebraMap F F' (B.repr (c f) j • f) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun f _ => hterm j f
      _ = ∑ j ∈ S, algebraMap K' F' (B j) * algebraMap F F' (g j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← Finset.mul_sum, ← map_sum, ← hgj]
      _ = ∑ j ∈ g.support, algebraMap K' F' (B j) * algebraMap F F' (g j) :=
          (Finset.sum_subset hgsub fun j _ hj => by
            rw [Finsupp.notMem_support_iff.mp hj, map_zero, mul_zero]).symm

  have hgD : ∀ j, g j ∈ LSpace (K := K) D :=
    AlgebraicCurve.mem_riemannRochSpace_of_sum_basis_smul_algebraMap_mem_mapDomain
      K F K' F' hfg hfg' hgen lift hlift_ord hlift_inj D B B.linearIndependent g
      (hf'eq ▸ hf')

  rw [hf'eq]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [← Algebra.smul_def]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g j, hgD j, rfl⟩)

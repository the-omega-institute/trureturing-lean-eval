/-
Copyright (c) 2026. Released under Apache 2.0.
An actual calculation of the exact integral singular chains on the protected
convergent sequence. The identity-minus-successor-plus-infinity endomorphism
fails already on zeroth homology. No comparison or CW descent is a premise.
Reuses Mathlib's totally disconnected singular-chain computation (Andrew Yang)
and the preserved protected light-profinite maps, Apache-2.0.
-/
import CWComparison.TotallyDisconnectedSingularNaturality
import CWComparison.SequenceDifferenceLocalization
import CWSolid.ChainHomology

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits LightCondensed LightCondensed.Solid LightProfinite OnePoint
open AlgebraicTopology

namespace CWComparison

abbrev sequenceTop : TopCat.{0} := LightProfinite.toTopCat.obj ℕ∪{∞}
instance sequenceTop_totallyDisconnectedSpace : TotallyDisconnectedSpace sequenceTop :=
  inferInstanceAs (TotallyDisconnectedSpace (ℕ∪{∞} : LightProfinite))
abbrev sequenceTopShift : sequenceTop ⟶ sequenceTop :=
  LightProfinite.toTopCat.map LightProfinite.shift
abbrev sequenceTopInfinity : sequenceTop ⟶ sequenceTop :=
  LightProfinite.toTopCat.map sequenceInfinity

abbrev sequenceIntegralPoints : ModuleCat.{0} ℤ :=
  (sigmaConst.obj (ModuleCat.of ℤ ℤ)).obj (sequenceTop : Type)

/-- Actual coproduct map induced by the two continuous sequence maps. -/
def sequenceIntegralDifference : sequenceIntegralPoints ⟶ sequenceIntegralPoints :=
  𝟙 _ - (sigmaConst.obj (ModuleCat.of ℤ ℤ)).map (↾fun x => sequenceTopShift x) +
    (sigmaConst.obj (ModuleCat.of ℤ ℤ)).map (↾fun x => sequenceTopInfinity x)

/-- Sum the coefficients of the finite points and discard infinity. This
functional is on the genuine coproduct, so all elements have finite support. -/
def sequenceFiniteCoefficient : sequenceIntegralPoints ⟶ ModuleCat.of ℤ ℤ :=
  Sigma.desc (fun x : sequenceTop =>
    match x with
    | Option.none => (0 : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ)
    | Option.some _ => 𝟙 (ModuleCat.of ℤ ℤ))

theorem sequenceIntegralDifference_finiteCoefficient :
    sequenceIntegralDifference ≫ sequenceFiniteCoefficient = 0 := by
  have hs (x : sequenceTop) : sequenceTopShift x =
      (match x with
      | Option.none => Option.none
      | Option.some n => Option.some (n + 1)) := rfl
  have hc (x : sequenceTop) : sequenceTopInfinity x = Option.none := rfl
  apply Sigma.hom_ext
  intro x
  simp only [sequenceIntegralDifference, Preadditive.add_comp,
    Preadditive.sub_comp, Preadditive.comp_add, Preadditive.comp_sub,
    Category.comp_id, sequenceFiniteCoefficient, sigmaConst,
    Sigma.ι_comp_map'_assoc, Category.id_comp, Sigma.ι_comp_desc, comp_zero]
  simp only [TypeCat.ofHom_apply, Category.id_comp, Sigma.ι_comp_desc]
  rw [hs, hc]
  cases x <;> simp

theorem sequenceFiniteCoefficient_ne_zero : sequenceFiniteCoefficient ≠ 0 := by
  intro h
  have he := congrArg (fun f =>
    Sigma.ι (fun _ : sequenceTop => ModuleCat.of ℤ ℤ) (OnePoint.some 0) ≫ f) h
  simp only [sequenceFiniteCoefficient, Sigma.ι_comp_desc, comp_zero] at he
  have hv := ConcreteCategory.congr_hom he (1 : ℤ)
  norm_num at hv

/-- A genuine noninvertibility result on the ordinary integral point module. -/
theorem sequenceIntegralDifference_not_isIso : ¬ IsIso sequenceIntegralDifference := by
  intro h
  letI := h
  apply sequenceFiniteCoefficient_ne_zero
  apply (cancel_epi sequenceIntegralDifference).1
  simpa only [comp_zero] using sequenceIntegralDifference_finiteCoefficient

private theorem alternatingConst_reflects_quasiIsoAt_zero
    {A B : ModuleCat.{0} ℤ} (f : A ⟶ B)
    [QuasiIsoAt (ChainComplex.alternatingConst.map f) 0] :
    IsIso f := by
  let K := ChainComplex.alternatingConst.obj A
  let M := ChainComplex.alternatingConst.obj B
  let a : K ⟶ M := ChainComplex.alternatingConst.map f
  haveI : IsIso (K.homologyπ 0) := K.isIso_homologyπ 1 0 (by simp) (by simp [K])
  haveI : IsIso (M.homologyπ 0) := M.isIso_homologyπ 1 0 (by simp) (by simp [M])
  haveI : IsIso (HomologicalComplex.homologyMap a 0) := inferInstance
  haveI : IsIso (HomologicalComplex.cyclesMap a 0) := by
    haveI : IsIso (HomologicalComplex.cyclesMap a 0 ≫ M.homologyπ 0) := by
      rw [← HomologicalComplex.homologyπ_naturality]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (M.homologyπ 0)
  haveI : IsIso (a.f 0) := by
    haveI : IsIso (K.iCycles 0 ≫ a.f 0) := by
      rw [← HomologicalComplex.cyclesMap_i]
      infer_instance
    exact IsIso.of_isIso_comp_left (K.iCycles 0) _
  exact inferInstanceAs (IsIso (a.f 0))

abbrev sequenceIntegralChains :=
  (((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)).obj sequenceTop)

/-- This is the endomorphism of the EXACT singular chains induced by the
same linear combination of the actual continuous maps. -/
def sequenceSingularDifference : sequenceIntegralChains ⟶ sequenceIntegralChains :=
  𝟙 _ - (((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
    (ModuleCat.of ℤ ℤ)).map sequenceTopShift) +
      (((singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
        (ModuleCat.of ℤ ℤ)).map sequenceTopInfinity)

/-- The all-degree library chain computation identifies the actual map with
the ordinary point-coefficient map, not an assumed homology identification. -/
theorem sequenceSingularDifference_conjugacy :
    (singularChainComplexFunctorIsoOfTotallyDisconnectedSpace
      (ModuleCat.{0} ℤ) (ModuleCat.of ℤ ℤ) sequenceTop).inv ≫ sequenceSingularDifference =
      ChainComplex.alternatingConst.map sequenceIntegralDifference ≫
        (singularChainComplexFunctorIsoOfTotallyDisconnectedSpace
          (ModuleCat.{0} ℤ) (ModuleCat.of ℤ ℤ) sequenceTop).inv := by
  simp only [sequenceSingularDifference, Preadditive.comp_add, Preadditive.comp_sub,
    Category.comp_id, totallyDisconnectedSingularChainIso_naturality]
  apply HomologicalComplex.hom_ext
  intro n
  simp only [HomologicalComplex.comp_f, HomologicalComplex.add_f_apply,
    HomologicalComplex.sub_f_apply, ChainComplex.alternatingConst_map_f,
    sequenceIntegralDifference, Preadditive.add_comp, Preadditive.sub_comp,
    Category.id_comp]
  rfl

/-- Failure occurs in an actual homology degree, independently of resources,
CW choices, or any future derived construction. -/
theorem sequenceSingularDifference_not_quasiIso :
    ¬ QuasiIso sequenceSingularDifference := by
  intro h
  letI := h
  let e := singularChainComplexFunctorIsoOfTotallyDisconnectedSpace
    (ModuleCat.{0} ℤ) (ModuleCat.of ℤ ℤ) sequenceTop
  have he : e.inv ≫ sequenceSingularDifference ≫ e.hom =
      ChainComplex.alternatingConst.map sequenceIntegralDifference := by
    rw [← Category.assoc, sequenceSingularDifference_conjugacy,
      Category.assoc, e.inv_hom_id]
    apply HomologicalComplex.hom_ext
    intro n
    simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f]
    exact Category.comp_id _
  haveI : QuasiIso
      (ChainComplex.alternatingConst.map sequenceIntegralDifference) := by
    rw [← he]
    infer_instance
  exact sequenceIntegralDifference_not_isIso
    (alternatingConst_reflects_quasiIsoAt_zero sequenceIntegralDifference)

/-- The SAME map on the EXACT protected unbounded derived singular chains. -/
def sequenceSingularDerivedDifference :
    singularChainsLightCondAbDerivedFunctor.obj sequenceTop ⟶
      singularChainsLightCondAbDerivedFunctor.obj sequenceTop :=
  𝟙 _ - singularChainsLightCondAbDerivedFunctor.map sequenceTopShift +
    singularChainsLightCondAbDerivedFunctor.map sequenceTopInfinity

/-- Genuine noninvertibility in the protected unbounded derived category. -/
theorem sequenceSingularDerivedDifference_not_isIso :
    ¬ IsIso sequenceSingularDerivedDifference := by
  intro h
  let F := LightCondensed.discrete (ModuleCat.{0} ℤ)
  haveI : F.IsLeftAdjoint := (LightCondensed.discreteUnderlyingAdj _).isLeftAdjoint
  haveI : F.Additive := Functor.additive_of_preserves_binary_products F
  let a := (F.mapHomologicalComplex (.down ℕ)).map sequenceSingularDifference
  have he : sequenceSingularDerivedDifference =
      DerivedCategory.Q.map (HomologicalComplex.extendMap a ComplexShape.embeddingDownNat) := by
    change sequenceSingularDerivedDifference =
      (F.mapHomologicalComplex (.down ℕ) ⋙
        ComplexShape.embeddingDownNat.extendFunctor LightCondAb ⋙
          DerivedCategory.Q).map sequenceSingularDifference
    simp only [sequenceSingularDerivedDifference, sequenceSingularDifference,
      Functor.map_add, Functor.map_sub, Functor.map_id]
    simp only [Functor.comp_map, Functor.map_id]
    rw [(F.mapHomologicalComplex (.down ℕ)).map_id,
      (ComplexShape.embeddingDownNat.extendFunctor LightCondAb).map_id,
      DerivedCategory.Q.map_id]
    rfl
  have hq : QuasiIso
      (HomologicalComplex.extendMap a ComplexShape.embeddingDownNat) := by
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso LightCondAb _).1
    rwa [← he]
  have ha : QuasiIso a :=
    (HomologicalComplex.quasiIso_extendMap_iff a ComplexShape.embeddingDownNat).1 hq
  apply sequenceSingularDifference_not_quasiIso
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    sequenceSingularDifference F).1 ha

end CWComparison

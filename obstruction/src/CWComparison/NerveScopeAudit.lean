/- Exact natural nerve maps, actual fiber contraction and protected CW scope audit. Apache-2.0. -/
import CWComparison.LastVertexOperator
import CWComparison.SingularLastVertex
import CWComparison.SingularFiberContraction
import CWComparison.SingularResolutionFibers
import CWComparison.CWNoClosedPoint
import CWComparison.CWThickening
import CWComparison.CWThickeningDerived
import CWComparison.DiscreteSequenceDifference
import CWComparison.SequenceDifferenceLocalization
import CWComparison.TotallyDisconnectedSingularNaturality
import CWComparison.SequenceSingularObstruction
import CWComparison.ProtectedCWComparisonObstruction
open CategoryTheory Limits LightCondensed LightCondensed.Solid
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

#check CWComparison.lastVertexOperator
#print axioms CWComparison.lastVertexOperator

#check CWComparison.lastVertexOperator_whisker
#print axioms CWComparison.lastVertexOperator_whisker

#check CWComparison.singularLastVertexMap
#print axioms CWComparison.singularLastVertexMap

#check CWComparison.singularLastVertexMap_naturality
#print axioms CWComparison.singularLastVertexMap_naturality

#check CWComparison.singularNerveIntegralComparison
#print axioms CWComparison.singularNerveIntegralComparison

#check CWComparison.singularDiscreteNerveChainsIso
#print axioms CWComparison.singularDiscreteNerveChainsIso

#check CWComparison.singularDiscreteNerveComparison
#print axioms CWComparison.singularDiscreteNerveComparison

#check CWComparison.singularDiscreteNerveUnboundedComparison
#print axioms CWComparison.singularDiscreteNerveUnboundedComparison

#check CWComparison.initialNerveAugmented
#print axioms CWComparison.initialNerveAugmented

#check CWComparison.initialNerveExtraDegeneracy
#print axioms CWComparison.initialNerveExtraDegeneracy

#check CWComparison.singularResolutionFiber
#print axioms CWComparison.singularResolutionFiber

#check CWComparison.singularFiberIntegralAugmented
#print axioms CWComparison.singularFiberIntegralAugmented

#check CWComparison.singularFiberIntegralExtraDegeneracy
#print axioms CWComparison.singularFiberIntegralExtraDegeneracy

#check CWComparison.singularFiberIntegralHomotopyEquiv
#print axioms CWComparison.singularFiberIntegralHomotopyEquiv

#check CWComparison.singularFiberIntegralHomotopyEquiv_hom
#print axioms CWComparison.singularFiberIntegralHomotopyEquiv_hom

#check CWComparison.singularFiberIntegralAugmentation_quasiIso
#print axioms CWComparison.singularFiberIntegralAugmentation_quasiIso

#check CWComparison.cwComplexOfNoClosedSingleton
#print axioms CWComparison.cwComplexOfNoClosedSingleton

#check CWComparison.indiscreteDouble
#print axioms CWComparison.indiscreteDouble

#check CWComparison.indiscreteDouble_not_isClosed_singleton
#print axioms CWComparison.indiscreteDouble_not_isClosed_singleton

#check CWComparison.thickening_not_isClosed_singleton
#print axioms CWComparison.thickening_not_isClosed_singleton

#check CWComparison.thickeningCWComplex
#print axioms CWComparison.thickeningCWComplex

#check CWComparison.cwThickeningTopFunctor
#print axioms CWComparison.cwThickeningTopFunctor

#check CWComparison.cwThickeningProjection
#print axioms CWComparison.cwThickeningProjection

#check CWComparison.cwThickeningSection
#print axioms CWComparison.cwThickeningSection

#check CWComparison.cwThickeningSection_projection
#print axioms CWComparison.cwThickeningSection_projection

#check CWComparison.cwThickeningHomotopy
#print axioms CWComparison.cwThickeningHomotopy

#check CWComparison.cwThickeningCWFunctor
#print axioms CWComparison.cwThickeningCWFunctor

#check CWComparison.cwThickeningCWFunctor_comp_inclusion
#print axioms CWComparison.cwThickeningCWFunctor_comp_inclusion

#check CWComparison.derivedFreeThickeningProjection_isIso
#print axioms CWComparison.derivedFreeThickeningProjection_isIso

#check CWComparison.derivedFreeThickeningNatIso
#print axioms CWComparison.derivedFreeThickeningNatIso

#check CWComparison.singularChainsThickeningProjection_isIso
#print axioms CWComparison.singularChainsThickeningProjection_isIso

#check CWComparison.singularChainsThickeningNatIso
#print axioms CWComparison.singularChainsThickeningNatIso

#check CWComparison.discreteSequenceShift
#print axioms CWComparison.discreteSequenceShift

#check CWComparison.discreteSequenceTotal
#print axioms CWComparison.discreteSequenceTotal

#check CWComparison.discreteSequenceTotal_shift
#print axioms CWComparison.discreteSequenceTotal_shift

#check CWComparison.discreteSequenceDifference_not_surjective
#print axioms CWComparison.discreteSequenceDifference_not_surjective

#check CWComparison.sequenceInfinity
#print axioms CWComparison.sequenceInfinity

#check CWComparison.freeSequenceDifference
#print axioms CWComparison.freeSequenceDifference

#check CWComparison.freeSequenceDifference_retraction
#print axioms CWComparison.freeSequenceDifference_retraction

#check CWComparison.freeSequenceDifference_projection
#print axioms CWComparison.freeSequenceDifference_projection

#check CWComparison.freeSequenceDifference_split
#print axioms CWComparison.freeSequenceDifference_split

#check CWComparison.derivedAdjunction_oneMinusShift_isIso
#print axioms CWComparison.derivedAdjunction_oneMinusShift_isIso

#check CWComparison.derivedFreeSequenceDifference_isIso
#print axioms CWComparison.derivedFreeSequenceDifference_isIso

#check CWComparison.totallyDisconnectedSingularSet_inv_naturality
#print axioms CWComparison.totallyDisconnectedSingularSet_inv_naturality

#check CWComparison.totallyDisconnectedSingularChainIso_naturality
#print axioms CWComparison.totallyDisconnectedSingularChainIso_naturality

#check CWComparison.totallyDisconnectedSingularIntegralHomotopyEquiv
#print axioms CWComparison.totallyDisconnectedSingularIntegralHomotopyEquiv

#check CWComparison.totallyDisconnectedSingularIntegralAugmentation_quasiIso
#print axioms CWComparison.totallyDisconnectedSingularIntegralAugmentation_quasiIso

#check CWComparison.sequenceTop
#print axioms CWComparison.sequenceTop

#check CWComparison.sequenceTop_totallyDisconnectedSpace
#print axioms CWComparison.sequenceTop_totallyDisconnectedSpace

#check CWComparison.sequenceTopShift
#print axioms CWComparison.sequenceTopShift

#check CWComparison.sequenceTopInfinity
#print axioms CWComparison.sequenceTopInfinity

#check CWComparison.sequenceIntegralPoints
#print axioms CWComparison.sequenceIntegralPoints

#check CWComparison.sequenceIntegralDifference
#print axioms CWComparison.sequenceIntegralDifference

#check CWComparison.sequenceFiniteCoefficient
#print axioms CWComparison.sequenceFiniteCoefficient

#check CWComparison.sequenceIntegralDifference_finiteCoefficient
#print axioms CWComparison.sequenceIntegralDifference_finiteCoefficient

#check CWComparison.sequenceFiniteCoefficient_ne_zero
#print axioms CWComparison.sequenceFiniteCoefficient_ne_zero

#check CWComparison.sequenceIntegralDifference_not_isIso
#print axioms CWComparison.sequenceIntegralDifference_not_isIso

#check CWComparison.sequenceIntegralChains
#print axioms CWComparison.sequenceIntegralChains

#check CWComparison.sequenceSingularDifference
#print axioms CWComparison.sequenceSingularDifference

#check CWComparison.sequenceSingularDifference_conjugacy
#print axioms CWComparison.sequenceSingularDifference_conjugacy

#check CWComparison.sequenceSingularDifference_not_quasiIso
#print axioms CWComparison.sequenceSingularDifference_not_quasiIso

#check CWComparison.sequenceSingularDerivedDifference
#print axioms CWComparison.sequenceSingularDerivedDifference

#check CWComparison.sequenceSingularDerivedDifference_not_isIso
#print axioms CWComparison.sequenceSingularDerivedDifference_not_isIso

#check CWComparison.derivedFreeTopSequenceDifference_isIso
#print axioms CWComparison.derivedFreeTopSequenceDifference_isIso

#check CWComparison.protectedCWComparison_not_nonempty
#print axioms CWComparison.protectedCWComparison_not_nonempty

example : freeLightCondAbOfTopFunctor = topCatToLightCondSet ⋙ free ℤ := rfl

example : isCWTopCat = fun X : TopCat =>
    Nonempty (Topology.CWComplex (Set.univ : Set X)) := rfl

example : singularChainsLightCondAbDerivedFunctor =
    singularChainsLightCondAbComplexFunctor ⋙ DerivedCategory.Q := rfl

example : derivedInclusion = Functor.mapDerivedCategory isSolid.ι := rfl

example : singularChainsLightCondAbCWDerivedFunctor =
    CWTopCat.toTopCat ⋙ singularChainsLightCondAbDerivedFunctor := rfl

example (X : TopCat.{0}) : isCWTopCat (CWComparison.cwThickeningTopFunctor.obj X) :=
  ⟨CWComparison.thickeningCWComplex X⟩

example : CWComparison.cwThickeningCWFunctor ⋙ CWTopCat.toTopCat =
    CWComparison.cwThickeningTopFunctor := rfl

#check CWComparison.totalDerived_protectedCWComparison_not_nonempty
#print axioms CWComparison.totalDerived_protectedCWComparison_not_nonempty

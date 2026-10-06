import CWComparison.ProtectedCWComparisonObstruction
open CategoryTheory LightCondensed LightCondensed.Solid
#print CWComparison.protectedCWComparison_not_nonempty
#print axioms CWComparison.protectedCWComparison_not_nonempty
#print CWComparison.totalDerived_protectedCWComparison_not_nonempty
#print axioms CWComparison.totalDerived_protectedCWComparison_not_nonempty
example : derivedInclusion = Functor.mapDerivedCategory isSolid.ι := rfl
example : isCWTopCat = fun X : TopCat => Nonempty (Topology.CWComplex (Set.univ : Set X)) := rfl
example : singularChainsLightCondAbCWDerivedFunctor = CWTopCat.toTopCat ⋙ singularChainsLightCondAbDerivedFunctor := rfl

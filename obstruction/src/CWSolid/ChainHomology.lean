import ChallengeDeps

noncomputable section
open CategoryTheory Limits LightCondensed
namespace LightCondensed.Solid

instance discreteAb_preservesFiniteLimits :
    PreservesFiniteLimits (LightCondensed.discrete (ModuleCat ℤ)) := by
  dsimp [LightCondensed.discrete, constantSheaf]
  infer_instance

instance discreteAb_preservesFiniteColimits :
    PreservesFiniteColimits (LightCondensed.discrete (ModuleCat ℤ)) := by
  have : (LightCondensed.discrete (ModuleCat ℤ)).IsLeftAdjoint :=
    (LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).isLeftAdjoint
  infer_instance

/-- Reindexing the discrete integral singular chains computes the protected homology object
in every degree `-n`. No CW comparison is assumed or used here. -/
def singularChainsDerivedHomologyIso (X : TopCat) (n : ℕ) :
    (DerivedCategory.homologyFunctor LightCondAb (-(n : ℤ))).obj
      (singularChainsLightCondAbDerivedFunctor.obj X) ≅ singularHomologyLightCondAb X n := by
  let K := (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
    (ModuleCat.of ℤ ℤ)).obj X)
  let F := LightCondensed.discrete (ModuleCat ℤ)
  exact (DerivedCategory.homologyFunctorFactors LightCondAb (-(n : ℤ))).app _ ≪≫
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K).extendHomologyIso
      ComplexShape.embeddingDownNat (by rfl) ≪≫
    ((K.sc n).mapHomologyIso F)

end LightCondensed.Solid

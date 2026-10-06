/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in src/licenses/LICENSE.LeanCondensed.

Uses Hausdorff–Alexandroff (Vasilii Nesterov) and Mathlib's topology and
compactness of standard simplices (Joël Riou).
-/
import CWComparison.ProfiniteCover
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits LightCondensed Convexity TopologicalSpace

namespace CWComparison

/-- A genuine Cantor cover of any nonempty compact metrizable space. -/
def compactMetrizableCover (X : TopCat) [MetrizableSpace X] [CompactSpace X] [Nonempty X] :
    C(cantorProfinite, X) := by
  letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  let h := exists_nat_bool_continuous_surjective_of_compact X
  exact ⟨Classical.choose h, (Classical.choose_spec h).1⟩

theorem compactMetrizableCover_surjective (X : TopCat)
    [MetrizableSpace X] [CompactSpace X] [Nonempty X] :
    Function.Surjective (compactMetrizableCover X) := by
  letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  exact (Classical.choose_spec (exists_nat_bool_continuous_surjective_of_compact X)).2

theorem compactMetrizableCover_free_epi (X : TopCat)
    [MetrizableSpace X] [CompactSpace X] [Nonempty X] :
    Epi (LightCondensed.Solid.freeLightCondAbOfTopFunctor.map
      (TopCat.ofHom (compactMetrizableCover X))) :=
  profiniteCover_free_epi (compactMetrizableCover X) (compactMetrizableCover_surjective X)

/-- Metrizability is derived from the genuine weight-coordinate embedding. -/
instance simplex_metrizable (n : SimplexCategory) :
    MetrizableSpace (SimplexCategory.toTop.{0}.obj n) := by
  letI : MetrizableSpace (StdSimplex ℝ (Fin (n.len + 1))) :=
    (StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n.len + 1))).metrizableSpace
  exact (Topology.IsEmbedding.uliftDown (X := StdSimplex ℝ (Fin (n.len + 1)))).metrizableSpace

instance simplex_compact (n : SimplexCategory) :
    CompactSpace (SimplexCategory.toTop.{0}.obj n) :=
  inferInstanceAs (CompactSpace (ULift (StdSimplex ℝ (Fin (n.len + 1)))))

/-- Each protected topological standard simplex has an actual light-profinite cover. -/
def simplexCantorCover (n : SimplexCategory) :
    C(cantorProfinite, SimplexCategory.toTop.{0}.obj n) :=
  compactMetrizableCover _

theorem simplexCantorCover_surjective (n : SimplexCategory) :
    Function.Surjective (simplexCantorCover n) :=
  compactMetrizableCover_surjective _

/-- Every free standard simplex is a genuine quotient of a free Cantor object. -/
theorem simplexCantorCover_free_epi (n : SimplexCategory) :
    Epi (LightCondensed.Solid.freeLightCondAbOfTopFunctor.map
      (TopCat.ofHom (simplexCantorCover n))) :=
  compactMetrizableCover_free_epi _

end CWComparison

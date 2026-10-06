/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in src/licenses/LICENSE.LeanCondensed.
-/
import CWSolid.Early
import Mathlib.AlgebraicTopology.TopologicalSimplex
import Mathlib.Topology.Homotopy.Basic

noncomputable section
open CategoryTheory LightCondensed.Solid

namespace CWComparison

/-- The actual free condensed prism of a topological space. -/
abbrev freePrism (X : TopCat) : LightCondAb :=
  freeLightCondAbOfTopFunctor.obj (TopCat.of (unitInterval × X))

/-- The free endpoint inclusion, with its original topology. -/
def freePrismEndpoint (X : TopCat) (t : unitInterval) :
    freeLightCondAbOfTopFunctor.obj X ⟶ freePrism X :=
  freeLightCondAbOfTopFunctor.map
    (TopCat.ofHom ⟨fun x => (t, x), continuous_const.prodMk continuous_id⟩)

/-- Applying the protected free functor to the whole homotopy prism. -/
def freePrismMap {X Y : TopCat} {f g : X ⟶ Y}
    (H : ContinuousMap.Homotopy f.hom g.hom) : freePrism X ⟶
      freeLightCondAbOfTopFunctor.obj Y :=
  freeLightCondAbOfTopFunctor.map (TopCat.ofHom H.toContinuousMap)

@[simp]
theorem freePrismEndpoint_zero_comp {X Y : TopCat} {f g : X ⟶ Y}
    (H : ContinuousMap.Homotopy f.hom g.hom) :
    freePrismEndpoint X 0 ≫ freePrismMap H = freeLightCondAbOfTopFunctor.map f := by
  rw [freePrismEndpoint, freePrismMap, ← Functor.map_comp]
  congr 1
  ext x
  exact H.map_zero_left x

@[simp]
theorem freePrismEndpoint_one_comp {X Y : TopCat} {f g : X ⟶ Y}
    (H : ContinuousMap.Homotopy f.hom g.hom) :
    freePrismEndpoint X 1 ≫ freePrismMap H = freeLightCondAbOfTopFunctor.map g := by
  rw [freePrismEndpoint, freePrismMap, ← Functor.map_comp]
  congr 1
  ext x
  exact H.map_one_left x

/-- A contraction of the exact topological standard simplex to its zeroth vertex.
This is topological data, not a chain homotopy of degree-zero free objects. -/
def simplexContraction (n : SimplexCategory) :
    ContinuousMap.Homotopy (ContinuousMap.id (SimplexCategory.toTop.{0}.obj n))
      (ContinuousMap.const _ (ULift.up (Convexity.StdSimplex.single
        (R := ℝ) (0 : Fin (n.len + 1))))) where
  toFun p := ULift.up (Convexity.convexCombPair (R := ℝ)
    (X := Convexity.StdSimplex ℝ (Fin (n.len + 1)))
    (unitInterval.symm p.1) p.1 (unitInterval.nonneg _) (unitInterval.nonneg _)
    (by simp) p.2.down (Convexity.StdSimplex.single 0))
  continuous_toFun := by
    apply continuous_uliftUp.comp
    rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ
      (Fin (n.len + 1))).continuous_iff]
    unfold Function.comp
    apply continuous_pi
    intro i
    simp only [unitInterval.coe_symm_eq, Convexity.StdSimplex.weights_convexCombPair,
      Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    fun_prop
  map_zero_left x := by
    apply ULift.ext
    simp
  map_one_left x := by
    apply ULift.ext
    simp
    rfl

/-- On the free simplex, the contraction restricts to the identity at zero. -/
@[simp]
theorem freeSimplexContraction_zero (n : SimplexCategory) :
    freePrismEndpoint (SimplexCategory.toTop.obj n) 0 ≫
      freePrismMap (f := 𝟙 (SimplexCategory.toTop.obj n))
        (g := TopCat.ofHom (X := SimplexCategory.toTop.obj n)
          (Y := SimplexCategory.toTop.obj n) (ContinuousMap.const _ _)) (simplexContraction n) =
      𝟙 _ := by
  rw [freePrismEndpoint_zero_comp]
  exact freeLightCondAbOfTopFunctor.map_id _

end CWComparison

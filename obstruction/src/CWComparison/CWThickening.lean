/-
Copyright (c) 2026. Released under Apache 2.0.
A source-level check of the exact protected CW scope, using the genuine pinned
classical CWComplex definition. No predicate or singular chain model is changed.
-/
import CWComparison.CWNoClosedPoint
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Homotopy.Basic

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Set

namespace CWComparison

/-- Doubling each point by an indiscrete two-point fiber eliminates all closed
singletons, without changing the space up to actual continuous homotopy. -/
theorem thickening_not_isClosed_singleton {X : Type} [TopologicalSpace X]
    (z : X × indiscreteDouble) : ¬ IsClosed ({z} : Set (X × indiscreteDouble)) := by
  intro hz
  have hc : Continuous (fun b : indiscreteDouble => (z.1, b)) :=
    continuous_const.prodMk continuous_id
  have hb := hz.preimage hc
  apply indiscreteDouble_not_isClosed_singleton z.2
  have he : (fun b : indiscreteDouble => (z.1, b)) ⁻¹' {z} = {z.2} := by
    ext b
    simp only [mem_preimage, mem_singleton_iff]
    constructor
    · exact fun h => congrArg Prod.snd h
    · intro h
      subst b
      exact Prod.mk.eta
  rw [he] at hb
  exact hb

/-- These spaces satisfy the exact classical CW predicate, in zero dimensions,
for every original topological space. This exposes the actual protected scope. -/
@[instance_reducible]
def thickeningCWComplex (X : Type) [TopologicalSpace X] :
    Topology.CWComplex (univ : Set (X × indiscreteDouble)) :=
  cwComplexOfNoClosedSingleton thickening_not_isClosed_singleton

/-- The actual thickening is functorial on every continuous map. -/
def cwThickeningTopFunctor : TopCat ⥤ TopCat where
  obj X := TopCat.of (X × indiscreteDouble)
  map f := TopCat.ofHom {
    toFun := fun z => (f z.1, z.2)
    continuous_toFun := (f.hom.continuous.comp continuous_fst).prodMk continuous_snd }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Natural projection from the actual thickening. -/
def cwThickeningProjection : cwThickeningTopFunctor ⟶ 𝟭 TopCat where
  app X := TopCat.ofHom ⟨Prod.fst, continuous_fst⟩
  naturality {_ _} _ := rfl

/-- Natural section selecting the false point of each indiscrete fiber. -/
def cwThickeningSection : 𝟭 TopCat ⟶ cwThickeningTopFunctor where
  app X := TopCat.ofHom {
    toFun := fun x => (x, WithTopology.toTopology ⊤ false)
    continuous_toFun := continuous_id.prodMk continuous_const }
  naturality {_ _} _ := rfl

theorem cwThickeningSection_projection :
    cwThickeningSection ≫ cwThickeningProjection = 𝟙 (𝟭 TopCat) := rfl

/-- An actual continuous homotopy, not an assumed homotopy invariance result. -/
def cwThickeningHomotopy (X : TopCat) :
    ContinuousMap.Homotopy
      ((cwThickeningProjection.app X ≫ cwThickeningSection.app X).hom)
      ((𝟙 (cwThickeningTopFunctor.obj X) :
        cwThickeningTopFunctor.obj X ⟶ cwThickeningTopFunctor.obj X)).hom where
  toFun z := (z.2.1,
    if z.1 = 0 then WithTopology.toTopology ⊤ false else z.2.2)
  continuous_toFun :=
    (continuous_fst.comp continuous_snd).prodMk continuous_of_indiscreteTopology
  map_zero_left _ := by simp [cwThickeningProjection, cwThickeningSection]; rfl
  map_one_left _ := by simp

end CWComparison

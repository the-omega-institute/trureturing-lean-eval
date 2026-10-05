import Mathlib
import LeanPool.HopfProblem.Threefold.SixSphereComplexAtlas

namespace Submission.Helpers

open scoped Manifold ContDiff

/-- Postcompose each chart with a continuous complex linear equivalence. -/
@[instance_reducible]
def changeModel {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (e : E ≃L[ℂ] F) (X : Type*)
    [TopologicalSpace X] [ChartedSpace E X] : ChartedSpace F X where
  atlas :=
    (fun c : OpenPartialHomeomorph X E => c.trans e.toHomeomorph.toOpenPartialHomeomorph) ''
      atlas E X
  chartAt x := (chartAt E x).trans e.toHomeomorph.toOpenPartialHomeomorph
  mem_chart_source x := by simp only [mfld_simps]
  chart_mem_atlas x := Set.mem_image_of_mem _ (chart_mem_atlas E x)

/-- The new transition maps are conjugates of the old ones by `e`. -/
theorem changeModel_isManifold {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (e : E ≃L[ℂ] F) (X : Type*)
    [TopologicalSpace X] [ChartedSpace E X] (n : ℕ∞ω) [IsManifold 𝓘(ℂ, E) n X] :
    letI := changeModel e X
    IsManifold 𝓘(ℂ, F) n X := by
  let := changeModel e X
  apply isManifold_of_contDiffOn
  rintro _ _ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
  have hcd : ContDiffOn ℂ n (c.symm.trans d) (c.symm.trans d).source := by
    simpa [contDiffPregroupoid] using
      ((contDiffGroupoid n 𝓘(ℂ, E)).compatible hc hd).1
  have hcomp :=
    e.contDiff.comp_contDiffOn
      (hcd.comp e.symm.contDiff.contDiffOn
        (show Set.MapsTo e.symm (e.symm ⁻¹' (c.symm.trans d).source)
          (c.symm.trans d).source from fun _ hy => hy))
  simpa [Set.preimage_preimage, Function.comp_def, OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.trans_target] using hcomp

/-- Select the atlas from the exact pinned analytic endpoint. Its sphere type is
definitionally the unit sphere in `EuclideanSpace ℝ (Fin 7)`. -/
@[instance_reducible]
noncomputable def euclideanAtlas :
    ChartedSpace (EuclideanSpace ℂ (Fin 3))
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 7)) 1) :=
  Classical.choose Mathoverflow1973.SixSphereComplexAtlas.exists_complex_analytic_atlas

/-- The selected atlas has the endpoint's analytic compatibility proof. -/
theorem euclideanAtlas_isManifold :
    letI := euclideanAtlas
    IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin 3)) ω
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 7)) 1) :=
  Classical.choose_spec Mathoverflow1973.SixSphereComplexAtlas.exists_complex_analytic_atlas

/-- Express the chosen atlas in the plain function model required by the challenge. -/
@[instance_reducible]
noncomputable def complexAtlas :
    ChartedSpace (Fin 3 → ℂ)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 7)) 1) := by
  letI := euclideanAtlas
  exact changeModel (EuclideanSpace.equiv (Fin 3) ℂ) _

/-- Passing to the function model preserves analytic compatibility. -/
theorem complexAtlas_isManifold :
    letI := complexAtlas
    IsManifold 𝓘(ℂ, Fin 3 → ℂ) ω
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 7)) 1) := by
  let := euclideanAtlas
  have := euclideanAtlas_isManifold
  exact changeModel_isManifold (EuclideanSpace.equiv (Fin 3) ℂ) _ ω

end Submission.Helpers

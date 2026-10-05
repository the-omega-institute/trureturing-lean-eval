import Mathlib

namespace Submission.Helpers

open Manifold
open scoped Manifold ContDiff

namespace ModelChange

-- Adapted from lean-pool LeanPool/HopfProblem/Threefold/SpecialPeriods7.lean,
-- Apache-2.0, Boris Alexeev.
@[instance_reducible]
def chartedSpace {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] (e : E ≃L[ℂ] F) (X : Type*)
    [TopologicalSpace X] [ChartedSpace E X] : ChartedSpace F X where
  atlas :=
    (fun c : OpenPartialHomeomorph X E => c.trans e.toHomeomorph.toOpenPartialHomeomorph) ''
      atlas E X
  chartAt x := (chartAt E x).trans e.toHomeomorph.toOpenPartialHomeomorph
  mem_chart_source x := by simp only [mfld_simps]
  chart_mem_atlas x := Set.mem_image_of_mem _ (chart_mem_atlas E x)

@[simp]
theorem chartAt_target {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] (e : E ≃L[ℂ] F) (X : Type*)
    [TopologicalSpace X] [ChartedSpace E X] (x : X) :
    letI := chartedSpace e X
    (chartAt F x).target = e.symm ⁻¹' (chartAt E x).target := by
  simp [chartAt, ChartedSpace.chartAt]

theorem isManifold {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] (e : E ≃L[ℂ] F) (X : Type*)
    [TopologicalSpace X] [ChartedSpace E X] (n : ℕ∞ω)
    [IsManifold (modelWithCornersSelf ℂ E) n X] :
    letI := chartedSpace e X
    IsManifold (modelWithCornersSelf ℂ F) n X := by
  let := chartedSpace e X
  apply isManifold_of_contDiffOn
  rintro _ _ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
  have hcd : ContDiffOn ℂ n (c.symm.trans d) (c.symm.trans d).source := by
    simpa [contDiffPregroupoid] using
      ((contDiffGroupoid n (modelWithCornersSelf ℂ E)).compatible hc hd).1
  have hcomp :=
    e.contDiff.comp_contDiffOn
      (hcd.comp e.symm.contDiff.contDiffOn
        (show Set.MapsTo e.symm (e.symm ⁻¹' (c.symm.trans d).source) (c.symm.trans d).source from
          fun _ hy => hy))
  simpa [Set.preimage_preimage, Function.comp_def, OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.trans_target] using hcomp

end ModelChange

end Submission.Helpers

import Mathlib
import Submission.Supplier.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Submission.Supplier.Definitions.Def_AlgebraicCurve_IsCurveOver
import Submission.Supplier.Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Submission.Supplier.Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Submission.Supplier.Definitions.Def_AlgebraicCurve_RegularDifferentials
import Submission.Supplier.Definitions.Def_AlgebraicCurve_ComplexLineIntegral
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_AlgebraicCurve_exists_path_forall_pathIntegral_eq_sum_mul

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

open AlgebraicCurve
open scoped Manifold ContDiff

theorem AlgebraicCurve.exists_path_forall_pathIntegral_eq_sum_mul
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F] [HasCanonicalDivisor (K := ℂ) (F := F)]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [CompactSpace (Place ℂ F)]
    [T2Space (Place ℂ F)] [ConnectedSpace (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    {ι : Type*} [Fintype ι] (T : Finset (Place ℂ F)) {Pz : ι → Place ℂ F}
    (Z : ∀ k, Path (Pz k) (Pz k)) (hZ : ∀ k t, Z k t ∉ T) (m : ι → ℤ)
    (Q₀ : Place ℂ F) (hQ₀ : Q₀ ∉ T) :
    ∃ α : Path Q₀ Q₀, (∀ t, α t ∉ T) ∧
      ∀ θ : Ω[F⁄ℂ], (∀ v : Place ℂ F, v ∉ T → 0 ≤ v.ordDifferential θ) →
        pathIntegral θ α = ∑ k, (m k : ℂ) * pathIntegral θ (Z k) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_exists_path_forall_pathIntegral_eq_sum_mul.solution

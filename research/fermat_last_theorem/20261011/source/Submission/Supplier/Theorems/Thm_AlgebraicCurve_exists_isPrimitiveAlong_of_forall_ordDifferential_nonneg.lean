import Mathlib
import Submission.Supplier.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Submission.Supplier.Definitions.Def_AlgebraicCurve_IsCurveOver
import Submission.Supplier.Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Submission.Supplier.Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Submission.Supplier.Definitions.Def_AlgebraicCurve_RegularDifferentials
import Submission.Supplier.Definitions.Def_AlgebraicCurve_ComplexLineIntegral
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_AlgebraicCurve_exists_isPrimitiveAlong_of_forall_ordDifferential_nonneg

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

open AlgebraicCurve
open scoped Manifold ContDiff Topology

theorem AlgebraicCurve.exists_isPrimitiveAlong_of_forall_ordDifferential_nonneg
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [T2Space (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    (η : Ω[F⁄ℂ]) {P Q : Place ℂ F} (γ : Path P Q)
    (hη : ∀ t : unitInterval, 0 ≤ (γ t).ordDifferential η) :
    (∃ g : unitInterval → ℂ, IsPrimitiveAlong η γ g) ∧
      ∀ g g' : unitInterval → ℂ, IsPrimitiveAlong η γ g → IsPrimitiveAlong η γ g' →
        ∀ t, g t - g' t = g 0 - g' 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_exists_isPrimitiveAlong_of_forall_ordDifferential_nonneg.solution

import Mathlib
import Submission.Supplier.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Submission.Supplier.Definitions.Def_AlgebraicCurve_IsCurveOver
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension_of_isAlgClosed

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

open AlgebraicCurve

theorem AlgebraicCurve.Place.exists_comap_algebraMap_eq_of_constantFieldExtension_of_isAlgClosed
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K F]
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (P : Place K F) :
    ∃ P' : Place K' F',
      P'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring ∧
      (∀ f : F, P'.ord (algebraMap F F' f) = P.ord f) ∧
      ∀ Q' : Place K' F',
        Q'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring → Q' = P' := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension_of_isAlgClosed.solution

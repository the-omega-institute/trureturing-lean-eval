import Mathlib
import Submission.Supplier.Definitions.Def_ModularCurve_X1
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

theorem ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange
    (L : Type*) [Field L] [Algebra ℚ L]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
    (hT : ModularGroup.T ∈ Γ) :
    ∃ x : ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ),
      Transcendental L x ∧
      FiniteDimensional
        (IntermediateField.adjoin L
          ({x} : Set (ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ))))
        (ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange.solution

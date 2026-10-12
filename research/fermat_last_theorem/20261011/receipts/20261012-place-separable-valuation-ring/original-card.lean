import Mathlib
import Submission.Supplier.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_ringHom_of_isSeparable

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

theorem AlgebraicCurve.Place.exists_toValuationSubring_eq_comap_ringHom_of_isSeparable {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F]
    (φ : F →+* F') (w : ValuationSubring F')
    (hwK : ∀ a : K, φ (algebraMap K F a) ∈ w) (hwx : ∃ y : F, φ y ∉ w) :
    ∃ v : AlgebraicCurve.Place K F, v.toValuationSubring = w.comap φ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_ringHom_of_isSeparable.solution

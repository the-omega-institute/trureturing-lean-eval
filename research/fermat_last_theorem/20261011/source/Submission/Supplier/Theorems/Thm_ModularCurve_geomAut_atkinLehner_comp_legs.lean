import Submission.Supplier.Definitions.Def_ModularCurve_AtkinLehnerPartial
import Submission.Supplier.Definitions.Def_ModularCurve_HeckeOperator
import Submission.Supplier.Definitions.Def_ModularCurve_GeometricBaseChange
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_ModularCurve_geomAut_atkinLehner_comp_legs

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

open ModularCurve
theorem ModularCurve.geomAut_atkinLehner_comp_legs (L : Type*) [Field L] [Algebra ℚ L] [Algebra.IsAlgebraic ℚ L] (N ℓ : ℕ) [NeZero N] [NeZero ℓ] (σ : modularFunctionFieldFull (N * ℓ) ≃ₐ[ℚ] modularFunctionFieldFull (N * ℓ)) (hσ : IsAtkinLehnerAutFull N ℓ σ) : (geomAut L (modularFunctionFieldFull (N * ℓ)) σ).toAlgHom.comp (heckeAlphaBar L N ℓ) = heckeBetaBar L N ℓ ∧ (geomAut L (modularFunctionFieldFull (N * ℓ)) σ).toAlgHom.comp (heckeBetaBar L N ℓ) = heckeAlphaBar L N ℓ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_geomAut_atkinLehner_comp_legs.solution

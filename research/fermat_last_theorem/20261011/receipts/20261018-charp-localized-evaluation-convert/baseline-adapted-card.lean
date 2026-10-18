import Submission.Supplier.Definitions.Def_ModularCurve_CharPReduction
import Submission.Supplier.Definitions.Def_ModularCurve_X0
import Mathlib.FieldTheory.Relrank
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_ModularCurve_CharPReduction_mem_or_inv_mem_modularLocalized

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

open ModularCurve CharPReduction
theorem ModularCurve.CharPReduction.mem_or_inv_mem_modularLocalized {L : Type*} [Field L] (A : ValuationSubring L)
    {k : Type*} [Field k] (red : A.toSubring →+* k) (N : ℕ) [NeZero N]
    (data : ModularPolynomialData N)
    (hdeg : (IntermediateField.adjoin k {(jqModC k : LaurentSeries k)}).relfinrank
      (modularFunctionFieldC k N) = dedekindPsi N)
    {f : LaurentSeries L}
    (hf : f ∈ IntermediateField.adjoin L {jqModC L, jqNModC L N}) :
    f ∈ modularLocalized N A.toSubring red ∨ f⁻¹ ∈ modularLocalized N A.toSubring red := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_CharPReduction_mem_or_inv_mem_modularLocalized.solution

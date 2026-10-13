import Submission.Supplier.Definitions.Def_ModularCurve_LaurentCoeff
import Submission.Supplier.Definitions.Def_ModularCurve_JqCoeff
import Mathlib.RingTheory.Valuation.ValuationRing
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_ModularCurve_coeffMap_mem_modularFunctionFieldC

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open ModularCurve
theorem ModularCurve.coeffMap_mem_modularFunctionFieldC {L : Type*} [Field L] (O : Subring L)
    [ValuationRing O] (hO : ∀ z : L, z ∈ O ∨ z⁻¹ ∈ O) {K : Type*} [Field K] (res : O →+* K)
    (N : ℕ) [NeZero N]
    (hdeg : Module.finrank (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
      (IntermediateField.adjoin (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
        ({jqNModC K N} : Set (LaurentSeries K))) = dedekindPsi N)
    {x : LaurentSeries L} (hx : x ∈ modularFunctionFieldC L N)
    (y : LaurentSeries O) (hy : coeffMap O.subtype y = x) :
    coeffMap res y ∈ modularFunctionFieldC K N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_coeffMap_mem_modularFunctionFieldC.solution

import Submission.Supplier.Definitions.Def_ModularCurve_OmegaOf
import Submission.Supplier.Definitions.Def_ModularCurve_EigenformIdeal
import Submission.Supplier.Definitions.Def_ModularCurve_HeckeModule
import Submission.Supplier.Definitions.Def_AlgebraicCurve_Differentials
import Submission.Supplier.Definitions.Def_CuspForm_IntegralStructure
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_omegaRow_T2

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
attribute [-simp] ModularCurve.jqNModC_one

open UpperHalfPlane ModularCurve AlgebraicCurve
theorem omegaRow_T2 :
    coeffMap (algebraMap ℚ ℂ) (thetaL ℚ jq) *
        ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
      = -(((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 2 *
          ((qExpansion 1 (ModularForm.E₆ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) := by p2m_exact_reverting @_root_.P2MW.S_omegaRow_T2.solution

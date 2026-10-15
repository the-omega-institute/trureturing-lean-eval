import Submission.Supplier.Definitions.Def_AutomorphicForm_BorelSubgroup
import Submission.Supplier.Definitions.Def_NumberField_AdelicLevel
import Submission.Supplier.Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_AutomorphicForm_exists_mem_adelicBorel_mul_eq

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
attribute [-instance] HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_submission FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_submission FixedPoints.instAddCommMonoidElemFixedPoints_submission
attribute [-simp] LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LocalGL2.swapUnit_val

open NumberField NumberField.AdelicLevel AutomorphicForm.WindowedSiegel

theorem AutomorphicForm.exists_mem_adelicBorel_mul_eq
    (F : Type) [Field F] [NumberField F] (g : AdelicGL2 (𝓞 F) F) :
    ∃ b k : AdelicGL2 (𝓞 F) F,
      b ∈ adelicBorel (𝓞 F) F ∧
      glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
      (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) ∧
      g = b * k := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_mem_adelicBorel_mul_eq.solution

#print axioms AutomorphicForm.exists_mem_adelicBorel_mul_eq

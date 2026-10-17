import Mathlib
import Submission.Supplier.Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Submission.Supplier.Definitions.Def_QuaternionAlgebra_Order
import Submission.Supplier.Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Submission.Supplier.Definitions.Def_Submodule_LocalBox
import Submission.Supplier.Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Submission.Supplier.Definitions.Def_QuaternionAlgebra_EichlerOrder
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_CerednikDrinfeld_classSetShift_mk_of_conjByFiniteIdele_eq

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem CerednikDrinfeld.classSetShift_mk_of_conjByFiniteIdele_eq
    {a b : ℚ} (O : Submodule ℤ ℍ[ℚ, a, b]) (hO : QuaternionAlgebra.IsOrder O)
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn : Submodule.conjByFiniteIdele O n = O) (x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    CerednikDrinfeld.classSetShift (Submodule.finiteIdeleStabilizer O) n
        (QuaternionAlgebra.ClassSet.mk (Submodule.finiteIdeleStabilizer O) x) =
      QuaternionAlgebra.ClassSet.mk (Submodule.finiteIdeleStabilizer O) (x * n) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_classSetShift_mk_of_conjByFiniteIdele_eq.solution

#print axioms CerednikDrinfeld.classSetShift_mk_of_conjByFiniteIdele_eq

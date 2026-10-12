import Mathlib
import Submission.Supplier.Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Submission.Supplier.Definitions.Def_QuaternionAlgebra_Order
import Submission.Supplier.Definitions.Def_Submodule_LocalBox
import Submission.Supplier.P2M.Util

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
namespace P2MW.S_CerednikDrinfeld_classSetForget_mk_of_le

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem solution
    {a b : ℚ} {U U' : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ} (h : U ≤ U') (x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    CerednikDrinfeld.classSetForget U U' (QuaternionAlgebra.ClassSet.mk U x) = QuaternionAlgebra.ClassSet.mk U' x := by
  obtain ⟨d, k, hd, hk, hout⟩ :=
    DoubleCoset.mk_out_eq_mul (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]).range U x
  obtain ⟨δ, rfl⟩ := MonoidHom.mem_range.mp k
  show ClassSet.mk U' (ClassSet.mk U x).out = _
  rw [show (ClassSet.mk U x).out = Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] δ * x * hd from hout,
    ClassSet.mk_mul_of_mem _ _ (h hk), ClassSet.mk_diagonal_mul]

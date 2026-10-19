import Mathlib
import Submission.Supplier.Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Submission.Supplier.Definitions.Def_QuaternionAlgebra_EichlerOrder
import Submission.Supplier.Definitions.Def_Submodule_LocalBox
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_CerednikDrinfeld_localBox_meetOrder_eq_of_isDefiniteRamifiedExactlyAt

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem CerednikDrinfeld.localBox_meetOrder_eq_of_isDefiniteRamifiedExactlyAt
    {a b : ℚ} {p : ℕ} [Fact p.Prime] (hdef : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b p)
    (R : Submodule ℤ ℍ[ℚ, a, b]) {M : ℕ} (hR : QuaternionAlgebra.IsEichlerOrder R M)
    (u : HeightOneSpectrum (𝓞 ℚ)) (hu : ((p : ℕ) : 𝓞 ℚ) ∈ u.asIdeal)
    (m : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    Submodule.localBox (CerednikDrinfeld.meetOrder R m) u = Submodule.localBox R u := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_localBox_meetOrder_eq_of_isDefiniteRamifiedExactlyAt.solution

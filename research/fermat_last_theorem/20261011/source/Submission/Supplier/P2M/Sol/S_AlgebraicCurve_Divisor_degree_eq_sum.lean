import Submission.Supplier.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Submission.Supplier.P2M.Util

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
namespace P2MW.S_AlgebraicCurve_Divisor_degree_eq_sum

open IsDedekindDomain WithZero IsLocalRing

noncomputable section

end

open AlgebraicCurve in
theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (D : Divisor K F) :
    Divisor.degree D = ∑ v ∈ D.support, D v * (v.deg : ℤ) :=
  Finsupp.liftAddHom_apply (fun v : Place K F => AddMonoidHom.mulRight (v.deg : ℤ)) D

end P2MW.S_AlgebraicCurve_Divisor_degree_eq_sum

#print axioms P2MW.S_AlgebraicCurve_Divisor_degree_eq_sum.solution

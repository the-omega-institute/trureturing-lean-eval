import Mathlib
import Submission.Supplier.Definitions.Def_AlgebraicCurve_IsCurveOver
import Submission.Supplier.Definitions.Def_ModularCurve_CanonicalDivisor
import Submission.Supplier.Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Submission.Supplier.Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
namespace P2MW.S_AlgebraicCurve_exists_mem_D_eq_smul_D_of_isCurveOver

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    [PerfectField K] [Algebra.EssFiniteType K F] [AlgebraicCurve.IsCurveOver K F]
    (v : AlgebraicCurve.Place K F) {π : F} (hπ : v.ord π = 1) {x : F} (hx : x ∈ v.toValuationSubring) :
    ∃ c : F, c ∈ v.toValuationSubring ∧ KaehlerDifferential.D K F x = c • KaehlerDifferential.D K F π := by
  exact _root_.P2MW.S_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver.AlgebraicCurve.exists_mem_D_eq_smul_D_of_isCurveOver_s12 v hπ hx

end P2MW.S_AlgebraicCurve_exists_mem_D_eq_smul_D_of_isCurveOver

#print axioms _root_.P2MW.S_AlgebraicCurve_exists_mem_D_eq_smul_D_of_isCurveOver.solution

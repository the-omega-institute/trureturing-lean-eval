import Submission.Supplier.Definitions.Def_ModularCurve_EtaQuotient
import Submission.Supplier.P2M.Util

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
namespace P2MW.S_ModularCurve_sharpUnitNecessary_of_eisensteinNumerator_eq_one

set_option autoImplicit false

noncomputable section

open Complex ModularGroup

open UpperHalfPlane hiding I

open scoped ModularForm MatrixGroups Real Topology

namespace DedekindEtaLog

section N

open ModularCurve

variable (ℓ : ℕ)

theorem sharpUnitNecessary_of_eisensteinNumerator_eq_one (h : eisensteinNumerator ℓ = 1) :
    SharpUnitNecessary ℓ :=
  fun m _ _ _ _ _ => h ▸ one_dvd m

end N

end DedekindEtaLog

end

theorem solution (ℓ : ℕ) (h : ModularCurve.eisensteinNumerator ℓ = 1) : ModularCurve.SharpUnitNecessary ℓ :=
  DedekindEtaLog.sharpUnitNecessary_of_eisensteinNumerator_eq_one ℓ h

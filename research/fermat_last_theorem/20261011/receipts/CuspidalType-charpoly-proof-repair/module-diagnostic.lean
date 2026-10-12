import Mathlib
import Submission.Supplier.Definitions.Def_CuspidalType_IsCuspidalOfType
import Submission.Supplier.P2M.Util
import Submission.Supplier.Definitions.Def_Compat_Mathlib430

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
namespace P2MW.S_CuspidalType_charpoly_ind_torus_eq_X_pow_orderOf_sub_one_pow

set_option autoImplicit false
set_option linter.unusedSectionVars false

p2m_open "Polynomial CuspidalType P2MW.S_CuspidalType_charpoly_ind_torus_eq_X_pow_orderOf_sub_one_pow.CuspidalType"
open scoped Matrix

namespace CuspidalType
p2m_export "CuspidalType" "GL2 ProjLine card_projLine ind quadBasis torus IsCuspidalOfType"
namespace IndTorus
p2m_open "CuspidalType"

p2m_open "Polynomial CuspidalType P2MW.S_CuspidalType_charpoly_ind_torus_eq_X_pow_orderOf_sub_one_pow.CuspidalType P2MW.S_CuspidalType_charpoly_ind_torus_eq_X_pow_orderOf_sub_one_pow.PermCharpoly"
open scoped Matrix

variable (q : ℕ) [Fact q.Prime]

local instance : Module (ZMod q) (Fin 2 → ZMod q) :=
  Pi.module (Fin 2) (fun _ => ZMod q) (ZMod q)

set_option pp.all true
#synth Module (ZMod q) (Fin 2 → ZMod q)
#check fun (v : Fin 2 → ZMod q) (hv : v ≠ 0) => Projectivization.mk (ZMod q) v hv
#check fun (v : Fin 2 → ZMod q) (hv : v ≠ 0) => (Projectivization.mk (ZMod q) v hv : ProjLine q)

import Submission.Supplier.Definitions.Def_CuspidalType_IsCuspidalOfType
import Mathlib.RepresentationTheory.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_CuspidalType_IsCuspidalOfType_dual

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

theorem CuspidalType.IsCuspidalOfType.dual
    {q : ℕ} [Fact q.Prime] {K : Type*} [Field K] [CharZero K] {θ : (GaloisField q 2)ˣ →* Kˣ}
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {ρ : Representation K (CuspidalType.GL2 q) V}
    (h : CuspidalType.IsCuspidalOfType θ ρ) :
    CuspidalType.IsCuspidalOfType θ ρ.dual := by p2m_exact_reverting @_root_.P2MW.S_CuspidalType_IsCuspidalOfType_dual.solution

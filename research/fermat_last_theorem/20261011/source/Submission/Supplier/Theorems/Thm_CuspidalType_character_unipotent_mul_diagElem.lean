import Submission.Supplier.Definitions.Def_CuspidalType_IsCuspidalOfType
import Mathlib.RepresentationTheory.Character
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_CuspidalType_character_unipotent_mul_diagElem

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open CuspidalType

theorem CuspidalType.character_unipotent_mul_diagElem
    {q : ℕ} [Fact q.Prime] {K : Type*} [Field K] [CharZero K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K (GL2 q) V)
    (hcusp : ∀ v : V, (∀ t : ZMod q, ρ (unipotent q t) v = v) → v = 0) {a : (ZMod q)ˣ} (ha : a ≠ 1) (s : ZMod q) :
    ρ.character (unipotent q s * diagElem q a) = 0 := by p2m_exact_reverting @_root_.P2MW.S_CuspidalType_character_unipotent_mul_diagElem.solution

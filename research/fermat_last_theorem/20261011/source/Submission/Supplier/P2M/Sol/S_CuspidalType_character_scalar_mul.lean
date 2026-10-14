import Submission.Supplier.Definitions.Def_CuspidalType_IsCuspidalOfType
import Mathlib.RepresentationTheory.Character
import Submission.Supplier.P2M.Util

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
namespace P2MW.S_CuspidalType_character_scalar_mul

set_option autoImplicit false

open CuspidalType

theorem solution
    {q : ℕ} [Fact q.Prime] {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K (GL2 q) V)
    (hcent : ∀ c : (ZMod q)ˣ, ρ (scalarElem q c) = LinearMap.id) (c : (ZMod q)ˣ) (g : GL2 q) :
    ρ.character (scalarElem q c * g) = ρ.character g := by
  simp only [Representation.character, map_mul, hcent c, Module.End.mul_eq_comp, LinearMap.id_comp]

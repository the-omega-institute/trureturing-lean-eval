import Submission.Supplier.Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_AutomorphicForm_typeSubmodule_inf_typeSubmodule_eq_bot

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

theorem AutomorphicForm.typeSubmodule_inf_typeSubmodule_eq_bot
    {H G : Type*} [Group H] [Group G]
    {W W' : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (ι : H →* G) (ρ : Representation ℂ H W) (ρ' : Representation ℂ H W')
    [ρ.IsIrreducible] [ρ'.IsIrreducible] (hne : IsEmpty (ρ.Equiv ρ')) :
    typeSubmodule ι ρ ⊓ typeSubmodule ι ρ' = ⊥ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_typeSubmodule_inf_typeSubmodule_eq_bot.solution

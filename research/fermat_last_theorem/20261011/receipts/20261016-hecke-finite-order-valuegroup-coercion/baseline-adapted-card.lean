import Submission.Supplier.Definitions.Def_HeckeCharacter_FiniteOrder
import Submission.Supplier.Definitions.Def_DirichletCharacter_DirichletIdeleChar
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_HeckeCharacter_IsFiniteOrderHeckeChar_exists_admitsModulus

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem HeckeCharacter.IsFiniteOrderHeckeChar.exists_admitsModulus
    {μ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ} (hμ : HeckeCharacter.IsFiniteOrderHeckeChar ℚ μ) :
    ∃ N : ℕ, N ≠ 0 ∧ HeckeCharacter.AdmitsModulus ℚ μ (Ideal.span {((N : ℕ) : 𝓞 ℚ)}) := by p2m_exact_reverting @_root_.P2MW.S_HeckeCharacter_IsFiniteOrderHeckeChar_exists_admitsModulus.solution

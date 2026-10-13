import Mathlib
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_ValuationSubring_exists_ringHom_extend_of_isAlgClosed

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

theorem ValuationSubring.exists_ringHom_extend_of_isAlgClosed
    {L Ω : Type*} [Field L] [Field Ω] [IsAlgClosed Ω] (R : Subring L) (φ : R →+* Ω) :
    ∃ (O : ValuationSubring L) (h : R ≤ O.toSubring) (ψ : O →+* Ω),
      ψ.comp (Subring.inclusion h) = φ ∧ RingHom.ker ψ = IsLocalRing.maximalIdeal O := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_ringHom_extend_of_isAlgClosed.solution

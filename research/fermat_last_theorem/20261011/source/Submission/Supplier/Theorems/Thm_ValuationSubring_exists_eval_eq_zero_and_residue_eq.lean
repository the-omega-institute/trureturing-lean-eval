import Mathlib
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_ValuationSubring_exists_eval_eq_zero_and_residue_eq

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

theorem ValuationSubring.exists_eval_eq_zero_and_residue_eq
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (q : Polynomial A) (hq : IsUnit q.leadingCoeff)
    (a₀ : IsLocalRing.ResidueField A)
    (hroot : (q.map (IsLocalRing.residue A)).eval a₀ = 0) :
    ∃ α : A, q.eval α = 0 ∧ IsLocalRing.residue A α = a₀ := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_eval_eq_zero_and_residue_eq.solution

#print axioms ValuationSubring.exists_eval_eq_zero_and_residue_eq

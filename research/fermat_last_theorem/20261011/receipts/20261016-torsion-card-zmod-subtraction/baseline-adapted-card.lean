import Mathlib
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_Submodule_natCard_torsionBySet_pow_linear_of_finite_torsionBy

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

theorem Submodule.natCard_torsionBySet_pow_linear_of_finite_torsionBy
    (T : Type*) [CommRing T] (G : Type*) [AddCommGroup G] [Module T G]
    (q : ℕ) [Fact q.Prime] (hfin : Finite ↥(Submodule.torsionBy ℤ G (q : ℤ)))
    (I : Ideal T) (hqI : (q : T) ∈ I) :
    ∃ e C : ℕ, ∀ m : ℕ,
      Nat.card ↥(Submodule.torsionBySet T G (↑(I ^ m) : Set T)) ≤ q ^ (m * e + C) ∧
        q ^ (m * e) ≤ Nat.card ↥(Submodule.torsionBySet T G (↑(I ^ m) : Set T)) * q ^ C := by p2m_exact_reverting @_root_.P2MW.S_Submodule_natCard_torsionBySet_pow_linear_of_finite_torsionBy.solution

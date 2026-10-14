import Submission.Supplier.Definitions.Def_CuspidalType_IsCuspidalOfType
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_CuspidalType_IsCuspidalOfType_exists_charpoly_eq_map_and_charpoly_ind_eq_X_sub_one_sq_mul_map

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false
open Polynomial

theorem
CuspidalType.IsCuspidalOfType.exists_charpoly_eq_map_and_charpoly_ind_eq_X_sub_one_sq_mul_map
    {q : ℕ} [Fact q.Prime] (p : ℕ) [Fact p.Prime]
    {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {θ : (GaloisField q 2)ˣ →* Kˣ} (hθ : θ ≠ 1) (hθp : ∃ n : ℕ, θ ^ p ^ n = 1)
    {ρ : Representation K (CuspidalType.GL2 q) V} (hρ : CuspidalType.IsCuspidalOfType θ ρ)
    (O : ValuationSubring K) (k : Type) [Field k] [CharP k p] (φ : O →+* k) (g : CuspidalType.GL2 q) :
    ∃ F : Polynomial O, LinearMap.charpoly (ρ g) = F.map O.subtype ∧
      LinearMap.charpoly (CuspidalType.ind q k g) = (X - 1) ^ 2 * F.map φ := by p2m_exact_reverting @_root_.P2MW.S_CuspidalType_IsCuspidalOfType_exists_charpoly_eq_map_and_charpoly_ind_eq_X_sub_one_sq_mul_map.solution

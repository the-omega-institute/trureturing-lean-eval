import Mathlib
import Submission.Supplier.Definitions.Def_QuaternionAlgebra_Order
import Submission.Supplier.P2M.Util

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
namespace P2MW.S_QuaternionAlgebra_IsOrder_finrank_eq_four

set_option autoImplicit false

open scoped Quaternion

theorem solution {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (hΛ : QuaternionAlgebra.IsOrder Λ) : Module.finrank ℤ Λ = 4 := by
  haveI : Submodule.IsLattice ℚ Λ := ⟨hΛ.fg, hΛ.spanTop⟩
  have hr : Module.rank ℤ Λ = Module.rank ℚ ℍ[ℚ, a, b] := Submodule.IsLattice.rank' ℚ Λ
  rw [QuaternionAlgebra.rank_eq_four] at hr
  exact Module.finrank_eq_of_rank_eq hr

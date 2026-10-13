import Mathlib
import Submission.Supplier.P2M.Util

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
namespace P2MW.S_RingHom_mem_range_of_pow_eq_one

theorem solution {F : Type*} [Field F] [IsAlgClosed F] [CharZero F]
    (σ : F →+* ℂ) {ζ : ℂ} {n : ℕ} (hn : 0 < n) (hζ : ζ ^ n = 1) : ζ ∈ σ.range := by
  haveI : NeZero n := ⟨hn.ne'⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.prim (M := F) (n := n)
  obtain ⟨i, -, hi⟩ := (hζ₀.map_of_injective σ.injective).eq_pow_of_pow_eq_one hζ
  exact ⟨ζ₀ ^ i, by rw [map_pow, hi]⟩

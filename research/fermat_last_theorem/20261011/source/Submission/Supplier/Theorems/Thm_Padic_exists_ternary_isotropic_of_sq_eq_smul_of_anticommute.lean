import Mathlib
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_Padic_exists_ternary_isotropic_of_sq_eq_smul_of_anticommute

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

theorem Padic.exists_ternary_isotropic_of_sq_eq_smul_of_anticommute {A : Type*} [AddCommGroup A] (ℓ : ℕ) [Fact ℓ.Prime] (hA : ∀ n : ℕ, Nonempty (ZMod (ℓ ^ n) × ZMod (ℓ ^ n) ≃+ Submodule.torsionBy ℤ A ((ℓ ^ n : ℕ) : ℤ))) (u v : ℤ) (i j : A →+ A) (hi : ∀ a, i (i a) = u • a) (hj : ∀ a, j (j a) = v • a) (hij : ∀ a, i (j a) = -(j (i a))) : ∃ z x y : ℚ_[ℓ], ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧ z ^ 2 - (u : ℚ_[ℓ]) * x ^ 2 - (v : ℚ_[ℓ]) * y ^ 2 = 0 := by p2m_exact_reverting @_root_.P2MW.S_Padic_exists_ternary_isotropic_of_sq_eq_smul_of_anticommute.solution

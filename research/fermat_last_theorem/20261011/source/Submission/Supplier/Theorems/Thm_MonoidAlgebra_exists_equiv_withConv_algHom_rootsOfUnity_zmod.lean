import Mathlib
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_MonoidAlgebra_exists_equiv_withConv_algHom_rootsOfUnity_zmod

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

theorem MonoidAlgebra.exists_equiv_withConv_algHom_rootsOfUnity_zmod
    (K : Type) [Field K] [CharZero K] (n : ℕ) [NeZero n] :
    ∃ eμ : WithConv (MonoidAlgebra K (Multiplicative (ZMod n)) →ₐ[K] AlgebraicClosure K)
        ≃ rootsOfUnity n (AlgebraicClosure K),
      (∀ f g, eμ (f * g) = eμ f * eμ g) ∧
      ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) f g,
        (∀ a, g a = σ (f a))
        → ((eμ g : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)
          = σ ((eμ f : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) := by p2m_exact_reverting @_root_.P2MW.S_MonoidAlgebra_exists_equiv_withConv_algHom_rootsOfUnity_zmod.solution

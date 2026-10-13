import Mathlib
import Submission.Supplier.Definitions.Def_GaloisRep_Flat
import Submission.Supplier.Definitions.Def_FLTPrelim_GaloisRep
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_PadicInt_exists_finiteFlat_kummerHopf_withConv_equiv_of_nnnorm_eq_one

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
attribute [-instance] PadicInt.KummerCarrier.instFreeA PadicInt.KummerCarrier.instFiniteA

open scoped NNReal
theorem PadicInt.exists_finiteFlat_kummerHopf_withConv_equiv_of_nnnorm_eq_one
    (p : ℕ) [Fact p.Prime] (u : ℚ_[p]) (hu : ‖u‖₊ = 1)
    (ζ η : AlgebraicClosure ℚ_[p]) (hζ : IsPrimitiveRoot ζ p)
    (hη : η ^ p = algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p]) u) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
      Module.Finite ℤ_[p] H ∧
      Module.Flat ℤ_[p] H ∧
      Coalgebra.IsCocomm ℤ_[p] H ∧
      ∃ ψ : (ZMod p × ZMod p) ≃ WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]),
        (∀ a b, ψ (a + b) = ψ a * ψ b) ∧
        ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) (e c : ℕ),
          σ ζ = ζ ^ e → σ η = ζ ^ c * η →
          ∀ (i j : ZMod p) (h : H),
            (ψ (e • i + c • j, j)) h = σ ((ψ (i, j)) h) := by p2m_exact_reverting @_root_.P2MW.S_PadicInt_exists_finiteFlat_kummerHopf_withConv_equiv_of_nnnorm_eq_one.solution

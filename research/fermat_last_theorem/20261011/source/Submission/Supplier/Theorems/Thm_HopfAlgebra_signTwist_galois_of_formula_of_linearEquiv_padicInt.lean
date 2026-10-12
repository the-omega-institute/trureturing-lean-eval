import Mathlib
import Submission.Supplier.Definitions.Def_GaloisRep_Flat
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_HopfAlgebra_signTwist_galois_of_formula_of_linearEquiv_padicInt

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

open scoped NNReal
open scoped TensorProduct in
theorem HopfAlgebra.signTwist_galois_of_formula_of_linearEquiv_padicInt
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (d : ℚ_[p]) (s : AlgebraicClosure ℚ_[p]) (hs0 : s ≠ 0)
    (hs : s ^ 2 = algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p]) d)
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H]
    (hcocomm : Coalgebra.IsCocomm ℤ_[p] H)
    (H' : Type) [CommRing H'] [HopfAlgebra ℤ_[p] H']
    (e : H' ≃ₗ[ℤ_[p]] H)
    (β : WithConv (H' →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) ≃
         WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]))
    (hβ : let Pm : H →ₗ[ℤ_[p]] H :=
        Ring.inverse (2:ℤ_[p]) • (LinearMap.id - HopfAlgebra.antipode ℤ_[p])
      ∀ (φ' : WithConv (H' →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])) (h : H),
        (β φ') h = φ' (e.symm (h - Pm h)) + s⁻¹ * φ' (e.symm (Pm h))) :
    ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
      (f' g' : WithConv (H' →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]))
      (g : WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])),
      (∀ h' : H', g' h' = σ (f' h')) →
      (∀ h : H, g h = σ ((β f') h)) →
        (σ s = s → β g' = g) ∧ (σ s ≠ s → β g' * g = 1) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_signTwist_galois_of_formula_of_linearEquiv_padicInt.solution

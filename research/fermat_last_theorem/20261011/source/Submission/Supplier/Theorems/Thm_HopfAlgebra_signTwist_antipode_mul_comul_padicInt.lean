import Mathlib
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_HopfAlgebra_signTwist_antipode_mul_comul_padicInt

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

open scoped TensorProduct
open scoped TensorProduct in
theorem HopfAlgebra.signTwist_antipode_mul_comul_padicInt
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (d₀ : ℤ_[p]) (hd₀ : IsUnit d₀)
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H]
    (hcocomm : Coalgebra.IsCocomm ℤ_[p] H) :
    let Pm : H →ₗ[ℤ_[p]] H :=
      Ring.inverse (2:ℤ_[p]) • (LinearMap.id - HopfAlgebra.antipode ℤ_[p])
    let Δ' : H →ₗ[ℤ_[p]] (H ⊗[ℤ_[p]] H) :=
      Coalgebra.comul + (Ring.inverse d₀ - 1) • ((TensorProduct.map Pm Pm).comp Coalgebra.comul)
    let μ'ₗ : (H ⊗[ℤ_[p]] H) →ₗ[ℤ_[p]] H :=
      LinearMap.mul' ℤ_[p] H + (d₀ - 1) • ((LinearMap.mul' ℤ_[p] H).comp (TensorProduct.map Pm Pm))
    (μ'ₗ ∘ₗ LinearMap.rTensor H (HopfAlgebra.antipode ℤ_[p]) ∘ₗ Δ'
        = (Algebra.linearMap ℤ_[p] H) ∘ₗ Coalgebra.counit)
    ∧ (μ'ₗ ∘ₗ LinearMap.lTensor H (HopfAlgebra.antipode ℤ_[p]) ∘ₗ Δ'
        = (Algebra.linearMap ℤ_[p] H) ∘ₗ Coalgebra.counit) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_signTwist_antipode_mul_comul_padicInt.solution

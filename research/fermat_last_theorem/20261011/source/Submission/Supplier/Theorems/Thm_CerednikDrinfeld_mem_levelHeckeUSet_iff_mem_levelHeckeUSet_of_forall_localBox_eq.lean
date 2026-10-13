import Mathlib
import Submission.Supplier.Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Submission.Supplier.Definitions.Def_QuaternionAlgebra_Order
import Submission.Supplier.Definitions.Def_Submodule_LocalBox
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_CerednikDrinfeld_mem_levelHeckeUSet_iff_mem_levelHeckeUSet_of_forall_localBox_eq

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem CerednikDrinfeld.mem_levelHeckeUSet_iff_mem_levelHeckeUSet_of_forall_localBox_eq
    {a b : ℚ} {Λ S R : Submodule ℤ ℍ[ℚ, a, b]}
    (hΛ : QuaternionAlgebra.IsOrder Λ) (hS : QuaternionAlgebra.IsOrder S) (hR : QuaternionAlgebra.IsOrder R)
    (hSR : S ≤ R) (hRΛ : R ≤ Λ) {ℓ : ℕ} (hℓ : ℓ ≠ 0)
    (hloc : ∀ v : HeightOneSpectrum (𝓞 ℚ), ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal → Submodule.localBox S v = Submodule.localBox R v)
    {β : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}
    (hβ : ∀ v : HeightOneSpectrum (𝓞 ℚ), ((ℓ : ℕ) : 𝓞 ℚ) ∉ v.asIdeal →
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (β : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) :
    β ∈ CerednikDrinfeld.levelHeckeUSet Λ S ℓ ↔ β ∈ CerednikDrinfeld.levelHeckeUSet Λ R ℓ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_mem_levelHeckeUSet_iff_mem_levelHeckeUSet_of_forall_localBox_eq.solution

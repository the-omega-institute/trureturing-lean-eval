import Mathlib
import Submission.Supplier.Definitions.Def_HeckeEis_BinaryFormRep
import Submission.Supplier.Definitions.Def_HeckeEis_EichlerIntegral
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_HeckeEis_IsEichlerIntegral_coeff_binaryFormRepSL_inv_apply_sub_eq_intervalIntegral_slash

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false

local macro "MvPolynomial.coeff" d:term:arg P:term:arg : term =>
  `(AddMonoidAlgebra.coeff $P $d)
local macro "MvPolynomial.coeff" d:term:arg : term =>
  `(fun P => AddMonoidAlgebra.coeff P $d)
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open scoped Manifold MatrixGroups ModularForm

theorem HeckeEis.IsEichlerIntegral.coeff_binaryFormRepSL_inv_apply_sub_eq_intervalIntegral_slash {n : ℕ}
    {f : UpperHalfPlane → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) {F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)}
    (hF : HeckeEis.IsEichlerIntegral n f F) (σ : SL(2, ℤ)) (h : ℤ) (τ : UpperHalfPlane) :
    MvPolynomial.coeff (Finsupp.single 1 n)
      ((HeckeEis.binaryFormRepSL ℂ n σ⁻¹
          (F ((σ * ModularGroup.T ^ h * σ⁻¹) • τ)
            - HeckeEis.binaryFormRepSL ℂ n (σ * ModularGroup.T ^ h * σ⁻¹) (F τ)) : ↥(HeckeEis.BinaryForm ℂ n)) :
        MvPolynomial (Fin 2) ℂ)
      = ∫ t in (0 : ℝ)..(h : ℝ), (f ∣[((n : ℤ) + 2)] σ) ((t : ℝ) +ᵥ (σ⁻¹ • τ)) := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_IsEichlerIntegral_coeff_binaryFormRepSL_inv_apply_sub_eq_intervalIntegral_slash.solution

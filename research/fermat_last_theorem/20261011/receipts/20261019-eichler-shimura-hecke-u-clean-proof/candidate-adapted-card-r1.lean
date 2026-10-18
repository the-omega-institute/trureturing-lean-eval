import Mathlib
import Submission.Supplier.Definitions.Def_HeckeEis_BinaryFormRep
import Submission.Supplier.Definitions.Def_Gamma0HeckeOperatorHom
import Submission.Supplier.Definitions.Def_Gamma0CoeffCohomology
import Submission.Supplier.Definitions.Def_HeckeEis_EichlerIntegral
import Submission.Supplier.Definitions.Def_ModularForm_HeckeOperatorForms
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_HeckeEis_eichlerShimuraMap_heckeULin

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open scoped Manifold MatrixGroups

theorem HeckeEis.eichlerShimuraMap_heckeULin (N : ℕ) [NeZero N] (n : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N)
    (T : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) →ₗ[ℂ]
      HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype))
    (hT : ∀ z : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
        ∃ w : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
          haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
          (w : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℂ n))
              = HeckeEis.coeffHeckeFun N ℓ ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) (HeckeEis.binaryFormAlphaAdj ℂ n ℓ) z ∧
            T (HeckeEis.coeffH1parMk _ z) = HeckeEis.coeffH1parMk _ w)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2)) :
    T (HeckeEis.eichlerShimuraMap n N f)
      = HeckeEis.eichlerShimuraMap n N (CuspForm.heckeULin ((n : ℤ) + 2) hℓN f) := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_eichlerShimuraMap_heckeULin.solution

#print axioms HeckeEis.eichlerShimuraMap_heckeULin

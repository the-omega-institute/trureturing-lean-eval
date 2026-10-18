import Mathlib
import Submission.Supplier.Definitions.Def_HeckeEis_BinaryFormRep
import Submission.Supplier.Definitions.Def_Gamma0CoeffCohomology
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_HeckeEis_exists_ne_zero_smul_eq_coeffH1par_map_int_rat

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.exists_ne_zero_smul_eq_coeffH1par_map_int_rat (n N : ℕ) [NeZero N]
    (Φ : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype)
        →+ HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℚ n).comp (CongruenceSubgroup.Gamma0 N).subtype))
    (hΦ : ∀ z : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
      ∃ w : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℚ n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
        (∀ g : CongruenceSubgroup.Gamma0 N,
            ((w : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℚ n)) g : MvPolynomial (Fin 2) ℚ)
              = MvPolynomial.map (Int.castRingHom ℚ)
                  (((z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℤ n)) g : MvPolynomial (Fin 2) ℤ))) ∧
        Φ (HeckeEis.coeffH1parMk _ z) = HeckeEis.coeffH1parMk _ w)
    (x : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℚ n).comp (CongruenceSubgroup.Gamma0 N).subtype)) :
    ∃ (m : ℤ) (y : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
      m ≠ 0 ∧ Φ y = m • x := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_exists_ne_zero_smul_eq_coeffH1par_map_int_rat.solution

import Mathlib
import Submission.Supplier.Definitions.Def_Gamma0CoeffCohomology
import Submission.Supplier.Definitions.Def_Gamma0CoeffCohomologyEigen
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_HeckeEis_exists_isEigensystemH1_one_natCast_mul_of_isEigensystemH1_one_of_three_dvd

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.exists_isEigensystemH1_one_natCast_mul_of_isEigensystemH1_one_of_three_dvd
    (M : ℕ) [NeZero M] (h3M : 3 ∣ M) (S₀ : Set ℕ) (κ : Type) [Field κ] [CharP κ 3] (nu : ℕ → κ)
    (hocc : HeckeEis.IsEigensystemH1 M (1 : Representation κ (CongruenceSubgroup.Gamma0 M) κ)
      (fun _ => LinearMap.id) S₀ nu) :
    ∃ M' : ℕ, M ∣ M' ∧ M' ∣ M * 3 ∧
      HeckeEis.IsEigensystemH1 M' (1 : Representation κ (CongruenceSubgroup.Gamma0 M') κ)
        (fun _ => LinearMap.id) (insert 3 S₀) (fun ℓ => (ℓ : κ) * nu ℓ) := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_exists_isEigensystemH1_one_natCast_mul_of_isEigensystemH1_one_of_three_dvd.solution

#print axioms HeckeEis.exists_isEigensystemH1_one_natCast_mul_of_isEigensystemH1_one_of_three_dvd

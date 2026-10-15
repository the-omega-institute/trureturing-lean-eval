import Mathlib
import Submission.Supplier.Definitions.Def_Gamma0CoeffCohomology
import Submission.Supplier.Definitions.Def_Gamma0CoeffCohomologyEigen
import Submission.Supplier.Definitions.Def_HeckeEis_Gamma0NebenRep
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_HeckeEis_exists_isEigensystemH1_one_of_isEigensystemH1_gamma0NebenRep

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.exists_isEigensystemH1_one_of_isEigensystemH1_gamma0NebenRep
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (S₀ : Set ℕ) (e t : ℕ)
    (het : (p - 1) ∣ e + 2 * t)
    (κ : Type) [Field κ] [CharP κ p] (nu : ℕ → κ)
    (hocc : HeckeEis.IsEigensystemH1 M (HeckeEis.gamma0NebenRep p M hpM κ e)
      (fun _ => LinearMap.id) S₀ nu) :
    ∃ (M' : ℕ) (mu : ℕ → κ), M ∣ M' ∧ M' ∣ M * p ∧
      HeckeEis.IsEigensystemH1 M' (1 : Representation κ (CongruenceSubgroup.Gamma0 M') κ)
        (fun _ => LinearMap.id) (insert p S₀) mu ∧
      ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ≠ p → ℓ ∉ S₀ → mu ℓ = (ℓ : κ) ^ t * nu ℓ := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_exists_isEigensystemH1_one_of_isEigensystemH1_gamma0NebenRep.solution

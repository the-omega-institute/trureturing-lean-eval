import Mathlib
import Definitions.Def_ModularForm_AtkinLehnerDatum
import P2M.Util
import P2M.Sol.S_ModularForm_AtkinLehnerDatum_nonempty_of_prime_of_dvd_of_not_sq_dvd

namespace P2MW.S_ModularForm_AtkinLehnerDatum_exists_mem_Gamma0_alGL_mul_eq

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open Matrix UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

theorem solution {M q : ℕ} [NeZero M]
    (W : ModularForm.AtkinLehnerDatum M q) {g : SL(2, ℤ)} (hg : g ∈ CongruenceSubgroup.Gamma0 M) :
    ∃ δ : SL(2, ℤ), δ ∈ CongruenceSubgroup.Gamma0 M ∧
      W.alGL * Matrix.SpecialLinearGroup.mapGL ℝ g = Matrix.SpecialLinearGroup.mapGL ℝ δ * W.alGL := by
  exact _root_.P2MW.S_ModularForm_AtkinLehnerDatum_nonempty_of_prime_of_dvd_of_not_sq_dvd.ModularForm.exists_cocycle_al W hg

end P2MW.S_ModularForm_AtkinLehnerDatum_exists_mem_Gamma0_alGL_mul_eq

import Submission.Supplier.Definitions.Def_ModularCurve_EtaQuotient
import Submission.Supplier.Definitions.Def_NumberTheory_DedekindSum
import Mathlib.Data.Int.ModEq
import Submission.Supplier.Theorems.Thm_ModularCurve_sharpUnitNecessary_of_witness
import Submission.Supplier.Theorems.Thm_rademacher_phi_level_witness_seven
import Submission.Supplier.P2M.Util

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
namespace P2MW.S_ModularCurve_sharpUnitNecessary_of_mod_twelve_eq_seven

set_option autoImplicit false

noncomputable section

open Complex ModularGroup

open UpperHalfPlane hiding I

open scoped ModularForm MatrixGroups Real Topology

namespace DedekindEtaLog

section N

open ModularCurve

variable (ℓ : ℕ) [NeZero ℓ]

private theorem _root_.DedekindEtaLog.sharpUnitNecessary_of_witness (hℓ : 2 ≤ ℓ) (a d : ℤ) (c' : ℕ) (hc' : 0 < c')
    (h1 : a * d ≡ 1 [ZMOD ((ℓ * c' : ℕ) : ℤ)]) (z₀ : ℤ)
    (hδ : 12 * (((a + d : ℤ) : ℚ) * (1 - (ℓ : ℚ)) / (12 * ((ℓ * c' : ℕ) : ℚ))
        + dedekindSum d c' - dedekindSum d (ℓ * c')) = ((Nat.gcd (ℓ - 1) 12 : ℕ) : ℚ) * z₀)
    (hcop : Nat.Coprime z₀.natAbs (eisensteinNumerator ℓ)) : SharpUnitNecessary ℓ :=
  ModularCurve.sharpUnitNecessary_of_witness ℓ hℓ a d c' hc' h1 z₀ hδ hcop

p2m_export "DedekindEtaLog" "sharpUnitNecessary_of_witness"
theorem etaPhase_witness_seven (j : ℕ) : 12 * ((((3 * j + 2 : ℕ) + 4 : ℤ) : ℚ) * (1 - ((12 * j + 7 : ℕ) : ℚ)) / (12 * ((12 * j + 7 : ℕ) : ℚ)) + dedekindSum 4 1 - dedekindSum 4 (12 * j + 7)) = ((Nat.gcd ((12 * j + 7) - 1) 12 : ℕ) : ℚ) * (-((j : ℤ) + 1)) ∧ Nat.Coprime (Int.natAbs (-((j : ℤ) + 1))) (((12 * j + 7) - 1) / Nat.gcd ((12 * j + 7) - 1) 12) :=
  rademacher_phi_level_witness_seven j

omit [NeZero ℓ] in
private lemma modEq_helper (ℓ : ℕ) (a d t : ℤ) (h : a * d = 1 + t * ℓ) :
    a * d ≡ 1 [ZMOD ((ℓ * 1 : ℕ) : ℤ)] :=
  Int.modEq_iff_dvd.2 ⟨-t, by push_cast; linear_combination -h⟩

theorem sharpUnitNecessary_of_mod_twelve_eq_seven (j : ℕ) : SharpUnitNecessary (12 * j + 7) := by
  haveI : NeZero (12 * j + 7) := ⟨by omega⟩
  obtain ⟨hδ, hcop⟩ := etaPhase_witness_seven j
  refine sharpUnitNecessary_of_witness (12 * j + 7) (by omega) ((3 * j + 2 : ℕ) : ℤ) 4 1 one_pos
    (modEq_helper _ _ _ 1 (by push_cast; ring)) (-((j : ℤ) + 1)) ?_ ?_
  · simpa only [mul_one, Int.cast_neg, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast,
      Int.cast_one] using hδ
  · exact hcop

end N

end DedekindEtaLog

end

theorem solution (j : ℕ) : ModularCurve.SharpUnitNecessary (12 * j + 7) :=
  DedekindEtaLog.sharpUnitNecessary_of_mod_twelve_eq_seven j

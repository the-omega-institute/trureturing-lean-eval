import P2M.Sol.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty

namespace P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_placeInfty_X_pow_eq_zero

set_option autoImplicit false

open _root_.AlgebraicCurve

theorem solution
    (K : Type*) [Field K] [PerfectField K] [DecidableEq (RatFunc K)]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar K (RatFunc K)]
    [∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
    (n : ℕ) :
    Algebra.trace K (AlgebraicCurve.RationalFunctionField.placeInfty K).ResidueField
        ((AlgebraicCurve.RationalFunctionField.placeInfty K).localResidue
          ((RatFunc.X : RatFunc K) ^ n
            * (AlgebraicCurve.RationalFunctionField.placeInfty K).differentialCoeff
                (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)))) = 0 := by
  have hv : _root_.AlgebraicCurve.RationalFunctionField.placeInfty K =
      _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField.placeInfty K := by
    apply _root_.AlgebraicCurve.Place.ext
    rfl
  rw [hv]
  let v := _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField.placeInfty K
  have hres : v.localResidue ((RatFunc.X : RatFunc K) ^ n
      * v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K))) = 0 := by
    change (HasCanonicalLocalResidueKStar.dataKStar v).res _ = 0
    rw [_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.X_pow_mul_differentialCoeff_D_X_eq_neg K n,
      _root_.map_neg, neg_eq_zero]
    have hsurj := _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.surjective_algebraMap_residueField_placeInfty K
    rcases CharP.char_is_prime_or_zero K (ringChar K) with hprime | hzero
    · have : Fact (ringChar K).Prime := ⟨hprime⟩
      exact _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.p0n22_cpf_res_differentialCoeff_D_mul_pow_inv_of_surj
        (p := ringChar K) v hsurj (RatFunc.X : RatFunc K)⁻¹
        (_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.ord_placeInfty_X_inv K)
        (HasCanonicalLocalResidueKStar.dataKStar v) (Nat.le_add_left 1 n)
    · have : CharP K 0 := hzero ▸ ringChar.charP K
      have : CharZero K := CharP.charP_to_charZero K
      exact _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.canonicalLocalResidueDataK_res_differentialCoeff_D_mul_pow_inv_placeInfty K
        (RatFunc.X : RatFunc K)⁻¹ (HasCanonicalLocalResidueKStar.dataKStar v)
        (Nat.le_add_left 1 n)
  change Algebra.trace K v.ResidueField _ = 0
  rw [hres, _root_.map_zero]

end P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_placeInfty_X_pow_eq_zero

import Submission.Supplier.P2M.Sol.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed
import Submission.Supplier.Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Submission.Supplier.Definitions.Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2

namespace P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_add_trace_localResidue_placeInfty_eq_zero

set_option autoImplicit false

open _root_.AlgebraicCurve
open Polynomial

theorem solution
    (K : Type*) [Field K] [PerfectField K] [DecidableEq (RatFunc K)]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar K (RatFunc K)]
    [∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
    {p c : K[X]} (hmon : p.Monic) (hp : Irreducible p) (hc : c.degree < p.degree) :
    Algebra.trace K (AlgebraicCurve.RationalFunctionField.finitePlace K hp).ResidueField
        ((AlgebraicCurve.RationalFunctionField.finitePlace K hp).localResidue
          (algebraMap K[X] (RatFunc K) c / algebraMap K[X] (RatFunc K) p
            * (AlgebraicCurve.RationalFunctionField.finitePlace K hp).differentialCoeff
                (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K))))
      + Algebra.trace K (AlgebraicCurve.RationalFunctionField.placeInfty K).ResidueField
        ((AlgebraicCurve.RationalFunctionField.placeInfty K).localResidue
          (algebraMap K[X] (RatFunc K) c / algebraMap K[X] (RatFunc K) p
            * (AlgebraicCurve.RationalFunctionField.placeInfty K).differentialCoeff
                (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)))) = 0 := by
  have hv : _root_.AlgebraicCurve.RationalFunctionField.placeInfty K =
      _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField.placeInfty K := by
    apply _root_.AlgebraicCurve.Place.ext
    rfl
  rw [hv]
  have hfmem := _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.p1MOneAtom_mul_differentialCoeff_mem_simplePole_finitePlace K
    (_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.dX_ne_zero K)
    (_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.p1DifferentialCoeffUnitFinite_dX_of_perfectField K) hp c hc
  have himem := _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.p1MOneAtom_mul_differentialCoeff_mem_simplePole_placeInfty K
    (_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.dX_ne_zero K)
    (_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.ordDifferential_placeInfty_D_ratFuncX K
      (_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.ordDifferentialWellDefined_ratFunc_of_perfectField K)) hp c hc
  have h := _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.p0n21_rtk_p1MOneSimplePoleCancel_dX_of_perfectField K
    p c hmon hp hc hfmem himem
  simp only [Place.localResidue]
  rw [(HasCanonicalLocalResidueKStar.dataKStar (_root_.AlgebraicCurve.RationalFunctionField.finitePlace K hp)).res_simplePole _ hfmem,
    (HasCanonicalLocalResidueKStar.dataKStar (_root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField.placeInfty K)).res_simplePole _ himem]
  simpa only [
    _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.p1PrincipalPartAtom, pow_one, _root_.P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.dX] using h

end P2MW.S_AlgebraicCurve_RationalFunctionField_trace_localResidue_finitePlace_add_trace_localResidue_placeInfty_eq_zero

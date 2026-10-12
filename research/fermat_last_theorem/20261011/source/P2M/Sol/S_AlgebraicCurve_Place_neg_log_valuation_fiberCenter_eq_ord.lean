import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel
import P2M.Sol.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed

namespace P2MW.S_AlgebraicCurve_Place_neg_log_valuation_fiberCenter_eq_ord

set_option autoImplicit false

open IsDedekindDomain WithZero IsLocalRing _root_.AlgebraicCurve _root_.AlgebraicCurve.Place

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] {v : Place K F} {w : Place K F'} (hw : w.restrict F = v) {x : F'} (hx : x ≠ 0) :
    -log ((fiberCenter F' v hw).valuation F' x) = w.ord x := by
  exact _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.neg_log_valuation_fiberCenter_eq_ord hw hx

end P2MW.S_AlgebraicCurve_Place_neg_log_valuation_fiberCenter_eq_ord

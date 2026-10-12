import P2M.Sol.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed

namespace P2MW.S_AlgebraicCurve_Place_ramificationIndex_eq_ramificationIdx_fiberCenter

set_option autoImplicit false

open _root_.AlgebraicCurve

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] (v : Place K F) {w : Place K F'}
    (hw : w.restrict F = v) :
    w.ramificationIndex F = (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx' (Place.fiberCenter F' v hw).asIdeal := by
  exact _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.ramificationIndex_eq_ramificationIdx_fiberCenter (v := v) hw

end P2MW.S_AlgebraicCurve_Place_ramificationIndex_eq_ramificationIdx_fiberCenter

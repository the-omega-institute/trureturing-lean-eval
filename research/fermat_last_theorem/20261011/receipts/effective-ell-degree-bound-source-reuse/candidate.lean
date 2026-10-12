import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel
import P2M.Sol.S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists

namespace P2MW.S_AlgebraicCurve_ell_le_degree_add_ellZero

set_option autoImplicit false

open _root_.AlgebraicCurve

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F] {D : Divisor K F}
    (hD : 0 ≤ D) [FiniteDimensional K ↥(LSpace (0 : Divisor K F))] :
    (ell D : ℤ) ≤ Divisor.degree D + ell (0 : Divisor K F) := by
  exact _root_.P2MW.S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.AlgebraicCurve.ell_le_degree_add_ellZero
    (K := K) (F := F) (D := D)
    (fun v => by simpa only [Finsupp.zero_apply] using (Finsupp.le_def.mp hD v))

end P2MW.S_AlgebraicCurve_ell_le_degree_add_ellZero

import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel
import P2M.Sol.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed

namespace P2MW.S_AlgebraicCurve_Place_eq_ord_of_addHom_of_nonneg_iff

set_option autoImplicit false

open _root_.AlgebraicCurve

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F) (φ : F → ℤ)
    (hmul : ∀ x y, x ≠ 0 → y ≠ 0 → φ (x * y) = φ x + φ y)
    (hone : ∃ t, t ≠ 0 ∧ φ t = 1)
    (hiff : ∀ x, x ≠ 0 → (0 ≤ φ x ↔ x ∈ w.toValuationSubring))
    {x : F} (hx : x ≠ 0) : φ x = w.ord x := by
  exact _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.Place.eq_ord_of_addHom_of_nonneg_iff w φ hmul hone hiff hx

end P2MW.S_AlgebraicCurve_Place_eq_ord_of_addHom_of_nonneg_iff

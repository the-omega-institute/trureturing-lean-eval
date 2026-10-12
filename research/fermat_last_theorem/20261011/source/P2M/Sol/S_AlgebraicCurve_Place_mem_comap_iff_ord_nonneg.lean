import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel

namespace P2MW.S_AlgebraicCurve_Place_mem_comap_iff_ord_nonneg

set_option autoImplicit false

open _root_.AlgebraicCurve

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F'] [Algebra F F'] {w : Place K F'} {f : F} (hf : f ≠ 0) :
    f ∈ w.toValuationSubring.comap (algebraMap F F') ↔
      0 ≤ w.ord (algebraMap F F' f) := by
  exact _root_.AlgebraicCurve.Place.mem_comap_iff_ord_nonneg (w := w) hf

end P2MW.S_AlgebraicCurve_Place_mem_comap_iff_ord_nonneg

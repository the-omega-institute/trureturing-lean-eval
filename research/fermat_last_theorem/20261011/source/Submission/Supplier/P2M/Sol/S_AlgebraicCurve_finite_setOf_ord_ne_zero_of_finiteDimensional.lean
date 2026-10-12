import Submission.Supplier.Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Submission.Supplier.Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel
import Submission.Supplier.P2M.Sol.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed

namespace P2MW.S_AlgebraicCurve_finite_setOf_ord_ne_zero_of_finiteDimensional

set_option autoImplicit false

open _root_.AlgebraicCurve

theorem solution {K F' : Type*} [Field K] [Field F'] [Algebra K F']
    [Algebra (RatFunc K) F'] [IsScalarTower K (RatFunc K) F'] [FiniteDimensional (RatFunc K) F'] [Algebra.IsSeparable (RatFunc K) F']
    {f : F'} (hf : f ≠ 0) : {w : Place K F' | w.ord f ≠ 0}.Finite := by
  exact _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.finite_setOf_ord_ne_zero_of_finiteDimensional hf

end P2MW.S_AlgebraicCurve_finite_setOf_ord_ne_zero_of_finiteDimensional

#print axioms P2MW.S_AlgebraicCurve_finite_setOf_ord_ne_zero_of_finiteDimensional.solution

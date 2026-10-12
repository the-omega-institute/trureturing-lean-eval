import Definitions.Def_AlgebraicCurve_IsCurveOver

namespace P2MW.S_AlgebraicCurve_one_le_deg

set_option autoImplicit false

open _root_.AlgebraicCurve

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F] (P : Place K F) : 1 ≤ P.deg := by
  have : Module.Finite K P.ResidueField := IsCurveOver.finite_residueField P
  exact Module.finrank_pos

end P2MW.S_AlgebraicCurve_one_le_deg

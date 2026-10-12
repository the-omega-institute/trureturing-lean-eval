import P2M.Sol.S_AlgebraicCurve_map_ne_zero_of_tame

-- Reuse the existing supplier theorem with the complete original solution declaration.
namespace P2MW.S_AlgebraicCurve_ordDifferential_map_eq

set_option autoImplicit false

open _root_.P2MW.S_AlgebraicCurve_map_ne_zero_of_tame.AlgebraicCurve

theorem solution {K : Type*} {F : Type*} {F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F']
    [IsCurveOver K F] [∀ v : Place K F, v.DCoordGenerates] [IsCurveOver K F'] [∀ w : Place K F', w.DCoordGenerates]
    (hreg : ∀ (w : Place K F') (u : F'), u ≠ 0 → w.ord u = 0 →
      w.differentialCoeff (KaehlerDifferential.D K F' u) = 0
        ∨ 0 ≤ w.ord (w.differentialCoeff (KaehlerDifferential.D K F' u)))
    (htame : ∀ w : Place K F', ((w.ramificationIndex F : ℕ) : F') ≠ 0)
    {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) (w : Place K F') :
    w.ordDifferential (KaehlerDifferential.map K K F F' ω₀)
      = (w.ramificationIndex F : ℤ) * (w.restrict F).ordDifferential ω₀
          + ((w.ramificationIndex F : ℤ) - 1) :=
  _root_.P2MW.S_AlgebraicCurve_map_ne_zero_of_tame.AlgebraicCurve.ordDifferential_map_eq (K := K) (F := F) (F' := F') hreg htame hω₀ w

end P2MW.S_AlgebraicCurve_ordDifferential_map_eq

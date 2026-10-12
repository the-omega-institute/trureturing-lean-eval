import P2M.Sol.S_AlgebraicCurve_map_ne_zero_of_tame

-- Reuse the existing supplier theorem with the complete original solution declaration.
namespace P2MW.S_AlgebraicCurve_two_mul_genus_sub_two_eq_of_degree_canonical

set_option autoImplicit false

open _root_.P2MW.S_AlgebraicCurve_map_ne_zero_of_tame.AlgebraicCurve

theorem solution {K : Type*} {F : Type*} {F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F']
    [IsCurveOver K F] [∀ v : Place K F, v.DCoordGenerates] [IsCurveOver K F'] [∀ w : Place K F', w.DCoordGenerates]
    [HasCanonicalDivisor (K := K) (F := F)] [HasCanonicalDivisor (K := K) (F := F')]
    [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    (hreg : ∀ (w : Place K F') (u : F'), u ≠ 0 → w.ord u = 0 →
      w.differentialCoeff (KaehlerDifferential.D K F' u) = 0
        ∨ 0 ≤ w.ord (w.differentialCoeff (KaehlerDifferential.D K F' u)))
    (htame : ∀ w : Place K F', ((w.ramificationIndex F : ℕ) : F') ≠ 0)
    {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) (hω₀' : KaehlerDifferential.map K K F F' ω₀ ≠ 0)
    (hK : Divisor.degree (canonicalDivisorOf (K := K) hω₀) = 2 * (genus K F : ℤ) - 2)
    (hK' : Divisor.degree (canonicalDivisorOf (K := K) hω₀') = 2 * (genus K F' : ℤ) - 2) :
    2 * (genus K F' : ℤ) - 2
      = (Module.finrank F F' : ℤ) * (2 * (genus K F : ℤ) - 2)
        + ∑ᶠ w : Place K F', ((w.ramificationIndex F : ℤ) - 1) * (w.deg : ℤ) :=
  _root_.P2MW.S_AlgebraicCurve_map_ne_zero_of_tame.AlgebraicCurve.two_mul_genus_sub_two_eq_of_degree_canonical (K := K) (F := F) (F' := F') hreg htame hω₀ hω₀' hK hK'

end P2MW.S_AlgebraicCurve_two_mul_genus_sub_two_eq_of_degree_canonical

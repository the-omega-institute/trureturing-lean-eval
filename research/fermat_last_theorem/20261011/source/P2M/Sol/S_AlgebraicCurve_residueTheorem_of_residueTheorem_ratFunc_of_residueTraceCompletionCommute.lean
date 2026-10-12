import P2M.Sol.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed

namespace P2MW.S_AlgebraicCurve_residueTheorem_of_residueTheorem_ratFunc_of_residueTraceCompletionCommute

set_option autoImplicit false

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [HasCanonicalLocalResidueKStar K F]
variable [HasCanonicalDivisor (K := K) (F := F)] [∀ w : Place K F, w.DCoordGenerates] [Nontrivial Ω[F⁄K]]
variable {E : Type*} [Field E] [Algebra K E] [HasCanonicalLocalResidueKStar K E]
variable [HasCanonicalDivisor (K := K) (F := E)] [∀ v : Place K E, v.DCoordGenerates] [Nontrivial Ω[E⁄K]]
variable [Algebra E F] [IsScalarTower K E F] [Algebra.IsIntegral E F]

omit [HasCanonicalDivisor (K := K) (F := F)] in
theorem kaehlerResidueTerm_smul_diagonal (g : F) (ω : Ω[F⁄K]) (f : F) (v : Place K F) :
    kaehlerResidueTerm (g • ω) (diagonalHom K F f) v = kaehlerResidueTerm ω (diagonalHom K F (g * f)) v := by
  unfold kaehlerResidueTerm
  simp only [diagonalHom_apply]
  rw [v.differentialCoeff_smul, show f * (g * v.differentialCoeff ω) = g * f * v.differentialCoeff ω by ring]

theorem residueTheorem_of_fiberKaehlerCotraceResidueIdentity
    [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]
    (hE : ResidueTheorem K E)
    {ωE₀ : Ω[E⁄K]} (hωE₀ : ωE₀ ≠ 0) (hgen : kaehlerPullback K F E ωE₀ ≠ 0)
    (hIdent : FiberKaehlerCotraceResidueIdentity K F E) :
    ResidueTheorem K F := by
  intro _ ωF hωF f
  rcases isEmpty_or_nonempty (Place K F) with hempty | hne
  · rw [weilOfKaehler_apply]
    exact finsum_eq_zero_of_forall_eq_zero fun w => (hempty.false w).elim
  obtain ⟨w₀⟩ := hne
  have hcoeff : w₀.differentialCoeff (kaehlerPullback K F E ωE₀) ≠ 0 := w₀.differentialCoeff_ne_zero hgen
  set c : F := w₀.differentialCoeff ωF * (w₀.differentialCoeff (kaehlerPullback K F E ωE₀))⁻¹ with hc
  have hωF_eq : ωF = c • kaehlerPullback K F E ωE₀ := by
    symm
    calc c • kaehlerPullback K F E ωE₀
        = c • (w₀.differentialCoeff (kaehlerPullback K F E ωE₀) • w₀.dCoord) := by
          rw [w₀.differentialCoeff_smul_dCoord]
      _ = (c * w₀.differentialCoeff (kaehlerPullback K F E ωE₀)) • w₀.dCoord := by rw [smul_smul]
      _ = w₀.differentialCoeff ωF • w₀.dCoord := by rw [hc, mul_assoc, inv_mul_cancel₀ hcoeff, mul_one]
      _ = ωF := w₀.differentialCoeff_smul_dCoord ωF
  have hterm : ∀ w : Place K F, kaehlerResidueTerm ωF (diagonalHom K F f) w
      = kaehlerResidueTerm (kaehlerPullback K F E ωE₀) (diagonalHom K F (c * f)) w := fun w => by
    conv_lhs => rw [hωF_eq]
    exact kaehlerResidueTerm_smul_diagonal c (kaehlerPullback K F E ωE₀) f w
  have hsup : (Function.support (kaehlerResidueTerm (kaehlerPullback K F E ωE₀) (diagonalHom K F (c * f)))).Finite :=
    kaehlerResidueTerm_support_finite_of_adeleSpace hgen (diagonal_mem_adeleSpace _)
  calc weilOfKaehler K F hωF ⟨diagonalHom K F f, diagonal_mem_adeleSpace f⟩
      = ∑ᶠ w : Place K F, kaehlerResidueTerm ωF (diagonalHom K F f) w := weilOfKaehler_apply hωF _
    _ = ∑ᶠ w : Place K F, kaehlerResidueTerm (kaehlerPullback K F E ωE₀) (diagonalHom K F (c * f)) w := finsum_congr hterm
    _ = ∑ᶠ v : Place K E, ∑ w ∈ v.fiber F, kaehlerResidueTerm (kaehlerPullback K F E ωE₀) (diagonalHom K F (c * f)) w :=
        finsum_place_eq_finsum_fiber_sum (E := E) _ hsup
    _ = ∑ᶠ v : Place K E, kaehlerResidueTerm ωE₀ (diagonalHom K E (Algebra.trace E F (c * f))) v :=
        finsum_congr fun v => hIdent hωE₀ hgen v _
    _ = 0 := by
        have h0 := hE hωE₀ (Algebra.trace E F (c * f))
        rw [weilOfKaehler_apply] at h0
        exact h0


end AlgebraicCurve

-- Preserve the original supplier telescope, including its overlapping class binders.
set_option linter.overlappingInstances false in
theorem solution
    {K F : Type*} [Field K] [PerfectField K] [DecidableEq (RatFunc K)]
    [Field F] [Algebra K F]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    [∀ w : AlgebraicCurve.Place K F, w.DCoordGenerates]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Algebra.IsIntegral (RatFunc K) F] [Module.Finite (RatFunc K) F]
    [∀ w : AlgebraicCurve.Place K F, w.FiniteResidue]
    [Nontrivial Ω[F⁄K]]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.IsCurveOver K (RatFunc K)]
    [∀ u : AlgebraicCurve.Place K (RatFunc K), u.FiniteResidue]
    [AlgebraicCurve.HasPrincipalDivisors K F] [Algebra.IsSeparable (RatFunc K) F]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := RatFunc K)]
    [Nontrivial Ω[(RatFunc K)⁄K]] [∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates]
    (hP1 : AlgebraicCurve.ResidueTheorem K (RatFunc K))
    (hRTCC : ModularCurve.KwF4R1V391a.KwF4R1V391aResidueTraceCompletionCommute K F (RatFunc K)) :
    AlgebraicCurve.ResidueTheorem K F := by
  classical
  exact AlgebraicCurve.residueTheorem_of_fiberKaehlerCotraceResidueIdentity (E := RatFunc K) hP1
    (_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.dX_ne_zero K)
    (_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.kaehlerPullback_eq_kaehlerCotrace (K := K) (F := F) (E := RatFunc K) (_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.dX K) ▸
      _root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.kaehlerCotrace_dX_ne_zero_of_isSeparable K F (_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.RationalFunctionField.placeInfty K))
    (_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.AlgebraicCurve.kw_es_fiberKaehlerCotraceResidueIdentity_of_RTCC_CTS hRTCC
      (_root_.P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.ModularCurve.KwF4R1V386a.kwF4R1V386a_completionTraceSum_of_isSeparable (K := K) (F := F) (E := RatFunc K)))

end P2MW.S_AlgebraicCurve_residueTheorem_of_residueTheorem_ratFunc_of_residueTraceCompletionCommute

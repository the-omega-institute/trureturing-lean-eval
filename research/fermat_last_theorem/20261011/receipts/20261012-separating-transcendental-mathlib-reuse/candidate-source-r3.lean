import Mathlib
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import P2M.Util
namespace P2MW.S_AlgebraicCurve_exists_separating_transcendental_of_perfectField

open IntermediateField

namespace AlgebraicCurve.SeparatingTranscendentalOfPerfectField

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem isTranscendenceBasis_of_transcendental {x : F} (hx : Transcendental K x)
    (hfd : FiniteDimensional K⟮x⟯ F) : IsTranscendenceBasis K (fun _ : Fin 1 => x) := by
  have hind : AlgebraicIndependent K (fun _ : Fin 1 => x) :=
    algebraicIndependent_unique_type_iff.mpr hx
  refine hind.isTranscendenceBasis_iff_isAlgebraic.mpr ?_
  have hr : Set.range (fun _ : Fin 1 => x) = ({x} : Set F) := by
    ext y
    simp [eq_comm]
  rw [hr, ← IntermediateField.isAlgebraic_adjoin_iff_top]
  have := hfd
  exact Algebra.IsAlgebraic.of_finite K⟮x⟯ F

theorem exists_separating [PerfectField K] {x : F} (hx : Transcendental K x)
    (hfd : FiniteDimensional K⟮x⟯ F) :
    ∃ t : F, Transcendental K t ∧ FiniteDimensional K⟮t⟯ F ∧ Algebra.IsSeparable K⟮t⟯ F := by
  classical
  have : Algebra.EssFiniteType K F :=
    _root_.AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional hx hfd
  obtain ⟨s, hs, hsep⟩ :=
    exists_isTranscendenceBasis_and_isSeparable_of_perfectField K F
  have hcard : s.card = 1 := by
    have h := hs.lift_cardinalMk_eq (isTranscendenceBasis_of_transcendental hx hfd)
    simpa only [Cardinal.mk_coe_finset, Cardinal.mk_fin, Cardinal.lift_natCast,
      Nat.cast_inj] using h
  obtain ⟨t, rfl⟩ := Finset.card_eq_one.mp hcard
  have ht : Transcendental K t :=
    (algebraicIndependent_singleton_iff (⟨t, by simp⟩ : ↥({t} : Finset F))).mp hs.1
  have hsep' : Algebra.IsSeparable K⟮t⟯ F := by
    rw [Finset.coe_singleton] at hsep
    exact hsep
  have : Algebra.EssFiniteType K⟮t⟯ F := Algebra.EssFiniteType.of_comp K K⟮t⟯ F
  have htfd : FiniteDimensional K⟮t⟯ F := Algebra.finite_of_essFiniteType_of_isAlgebraic
  exact ⟨t, ht, htfd, hsep'⟩

end AlgebraicCurve.SeparatingTranscendentalOfPerfectField

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K]
    {x : F} (htr : Transcendental K x)
    (hfd : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    ∃ t : F, Transcendental K t ∧
      FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F ∧
      Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) F :=
  AlgebraicCurve.SeparatingTranscendentalOfPerfectField.exists_separating htr hfd

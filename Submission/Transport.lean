import Submission.Measure
import ChallengeDeps

open Finset ProbabilityTheory unitInterval
open _root_.FractionalExpectationThresholds

namespace Submission.Helpers

variable {X α : Type*} [Fintype X] [Fintype α] [DecidableEq α]

noncomputable def setIso (e : X ≃ α) : Finset α ≃o Set X where
  toEquiv := Fintype.finsetEquivSet.trans e.symm.setCongr
  map_rel_iff' := by
    intro s t
    exact (Set.image_subset_image_iff e.symm.injective).trans Finset.coe_subset

omit [Fintype X] [DecidableEq α] in
lemma setIso_apply (e : X ≃ α) (t : Finset α) :
    setIso e t = e.symm '' (t : Set α) := rfl

omit [Fintype X] [DecidableEq α] in
lemma setIso_card (e : X ≃ α) (t : Finset α) : (setIso e t).ncard = t.card := by
  rw [setIso_apply, Set.ncard_image_of_injective _ e.symm.injective, Set.ncard_coe_finset]

noncomputable def family (e : X ≃ α) (𝓕 : Set (Set X)) : Finset (Finset α) := by
  classical
  exact univ.filter (fun t => setIso e t ∈ 𝓕)

omit [Fintype X] [DecidableEq α] in
lemma mem_family (e : X ≃ α) (𝓕 : Set (Set X)) (t : Finset α) :
    t ∈ family e 𝓕 ↔ setIso e t ∈ 𝓕 := by
  classical
  simp [family]

omit [Fintype X] in
lemma generate_minimals (e : X ≃ α) (𝓕 : Set (Set X)) (hu : IsUpperSet 𝓕) :
    KahnKalai.generate (KahnKalai.minimals (family e 𝓕)) = family e 𝓕 := by
  apply Finset.Subset.antisymm
  · intro t ht
    obtain ⟨s, hs, hst⟩ := KahnKalai.mem_generate.mp ht
    apply (mem_family e 𝓕 t).mpr
    exact hu ((setIso e).monotone hst)
      ((mem_family e 𝓕 s).mp (KahnKalai.minimals_subset _ hs))
  · exact KahnKalai.covers_minimals _

lemma minimal_card_le (𝓕 : Set (Set X)) (s : 𝓕) (hs : IsMin s) :
    (s : Set X).ncard ≤ l 𝓕 := by
  have hcard : ∀ t : Set X, t.ncard ≤ Fintype.card X := by
    intro t
    simpa using Set.ncard_le_ncard (Set.subset_univ t)
  have hb : BddAbove (Set.range (fun t : 𝓕 => ⨆ (_ : IsMin t), (t : Set X).ncard)) := by
    refine ⟨Fintype.card X, ?_⟩
    rintro _ ⟨t, rfl⟩
    by_cases ht : IsMin t
    · let : Nonempty (IsMin t) := ⟨ht⟩
      exact ciSup_le (fun _ => hcard t)
    · simp [ht]
  have hb' : BddAbove (Set.range (fun _ : IsMin s => (s : Set X).ncard)) :=
    ⟨Fintype.card X, by rintro _ ⟨_, rfl⟩; exact hcard s⟩
  exact (le_ciSup hb' hs).trans (le_ciSup hb s)

lemma minimals_bounded (e : X ≃ α) (𝓕 : Set (Set X)) :
    KahnKalai.IsBounded (KahnKalai.minimals (family e 𝓕)) (l 𝓕) := by
  intro t ht
  obtain ⟨htF, htmin⟩ := KahnKalai.mem_minimals.mp ht
  have htmem := (mem_family e 𝓕 t).mp htF
  have hmin : IsMin (⟨setIso e t, htmem⟩ : 𝓕) := by
    intro s hst
    have hst' : (setIso e).symm s.val ≤ t := by
      simpa using (setIso e).symm.monotone hst
    have hsF : (setIso e).symm s.val ∈ family e 𝓕 := by
      simpa only [mem_family, OrderIso.apply_symm_apply] using s.property
    have heq := htmin _ hsF hst'
    change setIso e t ⊆ s.val
    rw [← heq, OrderIso.apply_symm_apply]
  simpa only [setIso_card] using minimal_card_le 𝓕 ⟨setIso e t, htmem⟩ hmin

omit [DecidableEq α] in
lemma bernoulli_measure (e : X ≃ α) (𝓕 : Set (Set X)) (p : I) :
    setBer(Set.univ, p).real 𝓕 = KahnKalai.measureFamily p (family e 𝓕) := by
  classical
  have hm : setBer(Set.univ, p).real 𝓕 =
      ∑ s : Set X, if s ∈ 𝓕 then setBer(Set.univ, p).real {s} else 0 := by
    rw [← sum_filter]
    have heq : univ.filter (fun s : Set X => s ∈ 𝓕) = 𝓕.toFinset := by ext; simp
    rw [heq, MeasureTheory.sum_measureReal_singleton, Set.coe_toFinset]
  rw [hm]
  unfold KahnKalai.measureFamily family
  rw [sum_filter]
  apply Fintype.sum_equiv (setIso e).symm.toEquiv
  intro s
  have hcard : ((setIso e).symm s).card = s.ncard := by
    simpa using (setIso_card e ((setIso e).symm s)).symm
  change (if s ∈ 𝓕 then setBer(Set.univ, p).real {s} else 0) =
    if setIso e ((setIso e).symm s) ∈ 𝓕 then
      KahnKalai.measure p ((setIso e).symm s) else 0
  rw [OrderIso.apply_symm_apply]
  split_ifs with hs
  · rw [ProbabilityTheory.setBernoulli_real_singleton p (Set.subset_univ _) (Set.finite_univ)]
    simp [KahnKalai.measure, Set.ncard_sdiff' (Set.subset_univ s) (Set.finite_univ),
      hcard, Fintype.card_congr e]
  · rfl

end Submission.Helpers

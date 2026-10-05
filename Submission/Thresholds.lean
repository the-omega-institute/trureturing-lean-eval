import Submission.Transport

open Finset ProbabilityTheory unitInterval
open _root_.FractionalExpectationThresholds
open scoped NNReal

namespace Submission.Helpers

variable {X α : Type*} [Fintype X] [Fintype α] [DecidableEq α]

lemma chosen_threshold_le (e : X ≃ α) (𝓕 : Set (Set X)) (hu : IsUpperSet 𝓕) :
    (p_c 𝓕 : ℝ) ≤ KahnKalai.threshold (KahnKalai.minimals (family e 𝓕)) := by
  classical
  unfold p_c
  split_ifs with h
  · have hr := Classical.choose_spec h
    rw [bernoulli_measure e 𝓕] at hr
    apply root_le_threshold _ (Classical.choose h).property
    rw [generate_minimals e 𝓕 hu]
    convert hr using 1; norm_num
  · change 0 ≤ KahnKalai.threshold _
    exact Real.sInf_nonneg (fun _ hx => hx.1.1)

lemma cover_isWeaklySmall (e : X ≃ α) (𝓕 : Set (Set X)) (p : I)
    (G : Finset (Finset α)) (hG : KahnKalai.Covers G (family e 𝓕))
    (hcost : KahnKalai.expectation p G ≤ 1 / 2) : IsWeaklySmall p 𝓕 := by
  classical
  let g : Set X → ℝ≥0 := fun s => if (setIso e).symm s ∈ G then 1 else 0
  refine ⟨g, ?_, ?_⟩
  · intro T hT
    have ht : (setIso e).symm T ∈ family e 𝓕 := by
      simpa only [mem_family, OrderIso.apply_symm_apply] using hT
    obtain ⟨s, hsG, hsT⟩ := KahnKalai.mem_generate.mp (hG ht)
    have hsT' : setIso e s ⊆ T := by
      simpa using (setIso e).monotone hsT
    have hg : g (setIso e s) = 1 := by simp [g, hsG]
    rw [← hg]
    exact single_le_sum (fun _ _ => bot_le) (mem_filter.mpr ⟨mem_univ _, hsT'⟩)
  · have heq : (∑ s : Set X, (g s : ℝ) * (p : ℝ) ^ s.ncard) =
        KahnKalai.expectation p G := by
      have hfilter : univ.filter (fun t : Finset α => t ∈ G) = G := by ext; simp
      calc
        _ = ∑ t : Finset α, if t ∈ G then (p : ℝ) ^ t.card else 0 := by
          apply Fintype.sum_equiv (setIso e).symm.toEquiv
          intro s
          have hcard : ((setIso e).symm s).card = s.ncard := by
            simpa using (setIso_card e ((setIso e).symm s)).symm
          change (g s : ℝ) * (p : ℝ) ^ s.ncard =
            if (setIso e).symm s ∈ G then (p : ℝ) ^ ((setIso e).symm s).card else 0
          simp only [g, hcard]
          split_ifs <;> simp
        _ = KahnKalai.expectation p G := by rw [← sum_filter, hfilter]; rfl
    rw [heq]
    convert hcost using 1; norm_num

lemma integral_threshold_le_fractional (e : X ≃ α) (𝓕 : Set (Set X)) :
    KahnKalai.expectationThreshold (KahnKalai.minimals (family e 𝓕)) ≤ (q_f 𝓕 : ℝ) := by
  classical
  apply Real.sSup_le _ (q_f 𝓕).property.1
  intro p hp
  obtain ⟨G, hG, heq⟩ := KahnKalai.exists_cover_eq_coverCost p
    (KahnKalai.minimals (family e 𝓕))
  have hsmall : IsWeaklySmall (⟨p, hp.1⟩ : I) 𝓕 :=
    cover_isWeaklySmall e 𝓕 ⟨p, hp.1⟩ G (KahnKalai.covers_of_covers_minimals hG)
      (heq.trans_le hp.2)
  exact show (⟨p, hp.1⟩ : I) ≤ q_f 𝓕 from le_sSup hsmall

end Submission.Helpers

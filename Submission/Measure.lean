import LeanPool.KahnKalai.Cost
import LeanPool.KahnKalai.ParkPham
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite

open Finset

namespace Submission.Helpers

variable {α : Type*} [DecidableEq α]

def average (s : Finset α) (p : ℝ) (f : Finset α → ℝ) : ℝ :=
  ∑ t ∈ s.powerset, p ^ t.card * (1 - p) ^ (s.card - t.card) * f t

omit [DecidableEq α] in
lemma average_mono_function (s : Finset α) {p : ℝ} (hp : p ∈ Set.Icc 0 1)
    {f g : Finset α → ℝ} (h : ∀ t, f t ≤ g t) : average s p f ≤ average s p g := by
  apply sum_le_sum
  intro t _
  exact mul_le_mul_of_nonneg_left (h t)
    (mul_nonneg (pow_nonneg hp.1 _) (pow_nonneg (sub_nonneg.mpr hp.2) _))

lemma average_insert (s : Finset α) (a : α) (ha : a ∉ s) (p : ℝ)
    (f : Finset α → ℝ) :
    average (insert a s) p f =
      (1 - p) * average s p f + p * average s p (fun t => f (insert a t)) := by
  unfold average
  rw [sum_powerset_insert ha]
  have hcard : (insert a s).card = s.card + 1 := card_insert_of_notMem ha
  have hnot : ∀ t ∈ s.powerset, a ∉ t :=
    fun t ht hat => ha (mem_powerset.mp ht hat)
  simp only [hcard, mul_sum]
  apply congrArg₂ (· + ·)
  · apply sum_congr rfl
    intro t ht
    have hle := card_le_card (mem_powerset.mp ht)
    rw [show s.card + 1 - t.card = (s.card - t.card) + 1 by omega, pow_succ]
    ring
  · apply sum_congr rfl
    intro t ht
    rw [card_insert_of_notMem (hnot t ht), Nat.add_sub_add_right, pow_succ]
    ring

lemma average_mono_parameter (s : Finset α) (f : Finset α → ℝ) (hf : Monotone f) :
    MonotoneOn (fun p => average s p f) (Set.Icc 0 1) := by
  induction s using Finset.induction_on generalizing f with
  | empty => simp [average, MonotoneOn]
  | @insert a s ha ih =>
    intro p hp q hq hpq
    change average (insert a s) p f ≤ average (insert a s) q f
    rw [average_insert s a ha, average_insert s a ha]
    have h0 := ih f hf hp hq hpq
    have h1 := ih (fun t => f (insert a t))
      (fun _ _ h => hf (insert_subset_insert a h)) hp hq hpq
    have h01 := average_mono_function s hp (fun t => hf (subset_insert a t))
    have hfirst : (1 - p) * average s p f + p * average s p (fun t => f (insert a t)) ≤
        (1 - q) * average s p f + q * average s p (fun t => f (insert a t)) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hpq) (sub_nonneg.mpr h01)]
    exact hfirst.trans (add_le_add
      (mul_le_mul_of_nonneg_left h0 (sub_nonneg.mpr hq.2))
      (mul_le_mul_of_nonneg_left h1 hq.1))

variable [Fintype α]

lemma measureFamily_mono (F : Finset (Finset α)) :
    MonotoneOn (fun p => KahnKalai.measureFamily p (KahnKalai.generate F))
      (Set.Icc 0 1) := by
  let f : Finset α → ℝ := fun t => if t ∈ KahnKalai.generate F then 1 else 0
  have hf : Monotone f := by
    intro s t hst
    by_cases hs : s ∈ KahnKalai.generate F
    · simp [f, hs, KahnKalai.subset_mem_generate hst hs]
    · simp only [f, hs, ite_false]
      split <;> norm_num
  have heq : ∀ p, average univ p f = KahnKalai.measureFamily p (KahnKalai.generate F) := by
    intro p
    simp [average, f, KahnKalai.measureFamily, KahnKalai.measure,
      ← sum_filter, KahnKalai.generate]
  simpa only [heq] using average_mono_parameter univ f hf

lemma measureFamily_zero (A : Finset (Finset α)) :
    KahnKalai.measureFamily 0 A = if ∅ ∈ A then 1 else 0 := by
  classical
  unfold KahnKalai.measureFamily KahnKalai.measure
  by_cases h : ∅ ∈ A
  · rw [sum_eq_single ∅]
    · simp [h]
    · intro t _ ht
      simp [card_ne_zero.mpr (nonempty_iff_ne_empty.mpr ht)]
    · exact fun hn => (hn h).elim
  · rw [sum_eq_zero]
    · simp [h]
    · intro t ht
      have hne : t ≠ ∅ := fun he => h (he ▸ ht)
      simp [card_ne_zero.mpr (nonempty_iff_ne_empty.mpr hne)]

lemma root_le_threshold (F : Finset (Finset α)) {r : ℝ}
    (hr : r ∈ Set.Icc 0 1) (hroot : KahnKalai.measureFamily r (KahnKalai.generate F) = 1 / 2) :
    r ≤ KahnKalai.threshold F := by
  classical
  let A := KahnKalai.generate F
  let P : Polynomial ℝ := ∑ t ∈ A,
    Polynomial.X ^ t.card * (1 - Polynomial.X) ^ (Fintype.card α - t.card)
  have heval : ∀ p, P.eval p = KahnKalai.measureFamily p A := by
    intro p
    simp [P, Polynomial.eval_finsetSum, KahnKalai.measureFamily, KahnKalai.measure]
  apply le_csInf (show {p : ℝ | p ∈ Set.Icc 0 1 ∧
    1 / 2 ≤ KahnKalai.measureFamily p A}.Nonempty from ⟨r, hr, hroot.ge⟩)
  intro p hp
  by_contra hle
  have hpr : p < r := lt_of_not_ge hle
  have hconstant : ∀ x ∈ Set.Icc p r, P.eval x = (Polynomial.C (1 / 2 : ℝ)).eval x := by
    intro x hx
    have hxI : x ∈ Set.Icc 0 1 := ⟨hp.1.1.trans hx.1, hx.2.trans hr.2⟩
    have hlow := measureFamily_mono F hp.1 hxI hx.1
    have hhigh := measureFamily_mono F hxI hr hx.2
    rw [heval]
    simp only [Polynomial.eval_C]
    exact le_antisymm (hhigh.trans hroot.le) (hp.2.trans hlow)
  have hpoly : P = Polynomial.C (1 / 2 : ℝ) :=
    Polynomial.eq_of_infinite_eval_eq _ _ ((Set.Icc_infinite hpr).mono hconstant)
  have hzero : KahnKalai.measureFamily 0 A = 1 / 2 := by
    rw [← heval, hpoly, Polynomial.eval_C]
  rw [measureFamily_zero] at hzero
  split at hzero <;> norm_num at hzero

end Submission.Helpers

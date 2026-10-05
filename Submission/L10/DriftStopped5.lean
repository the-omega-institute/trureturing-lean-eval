import Submission.L10.DriftStopped4

/-!
# Gate L-10 (`klartag_packing`) — the stopped error's integral, and the drift side

Brief 59.  Reports 53, 55 and 57 each stopped on one named input; each was a hypothesis to name,
not a wall.  This module names them — `IntegrableAtIndex` (brief 58's, by domination against
`GaussianMaximal.maxNorm`) alongside `MaximalAtAdopted` and `SlackHyp` — and threads the
consequences.

## The two sums, and the identity that makes the second one a single term

`DriftStopped4.stoppedErr_split` bounds `stoppedErr k ω` by two terms, each `0` outside its case.
Summing over `k < m`:

* the **good range** term vanishes off the freeze set (`ChainWiring.chainErr_eq_zero_of_not_freezes`),
  so `ChainDrift.sum_err_le` bounds its sum by `(freeze count)·ε ≤ finrank E · ε`;
* the **middle** term's condition `k < τ ∧ ¬(k+1 ≤ τ−1)` pins `k` to the single value `τ − 1`
  (`mid_iff`), so its sum is *one* evaluation, at a random index — `MaximalHyp2`'s shape.

`mid_iff` is the whole reason the middle case costs `O(B)` and not `O(N·B)`.
-/


namespace Submission.L10.DriftStopped5

open MeasureTheory Matrix Finset Module Submission.L10 Submission.L10.Increments
open Submission.L10.StoppedChain Submission.L10.DriftStopped Submission.L10.DriftStopped4
open scoped RealInnerProductSpace

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι] {Ω : Type*} [MeasurableSpace Ω]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

/-! ## 1. The middle case is a single index -/

omit [Countable ι] [MeasurableSpace Ω] in
/-- **The middle case pins `k` to `τ − 1`.**  `k < τ` and `¬(k+1 ≤ τ−1)` force `τ−1 ≤ k < τ`. -/
theorem mid_iff {η r₀ c₃ : ℝ} {N k : ℕ} {ω : Ω}
    (hτ : 1 ≤ tau q W A₀ ξ η r₀ c₃ N ω) :
    (k < tau q W A₀ ξ η r₀ c₃ N ω ∧ ¬ (k + 1 ≤ tau q W A₀ ξ η r₀ c₃ N ω - 1))
      ↔ k = tau q W A₀ ξ η r₀ c₃ N ω - 1 := by
  constructor
  · rintro ⟨h1, h2⟩; omega
  · intro h; omega

omit [Countable ι] [MeasurableSpace Ω] in
/-- Summing the middle term is a single evaluation. -/
theorem sum_mid_eq {η r₀ c₃ : ℝ} {N m : ℕ} {ω : Ω} (g : ℕ → ℝ)
    (hτ : 1 ≤ tau q W A₀ ξ η r₀ c₃ N ω) :
    ∑ k ∈ Finset.range m,
        (if k < tau q W A₀ ξ η r₀ c₃ N ω ∧ ¬ (k + 1 ≤ tau q W A₀ ξ η r₀ c₃ N ω - 1)
          then g k else 0)
      = if tau q W A₀ ξ η r₀ c₃ N ω - 1 ∈ Finset.range m
          then g (tau q W A₀ ξ η r₀ c₃ N ω - 1) else 0 := by
  classical
  rw [← Finset.sum_ite_eq (Finset.range m) (tau q W A₀ ξ η r₀ c₃ N ω - 1) g]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases h : k = tau q W A₀ ξ η r₀ c₃ N ω - 1
  · rw [ite_eq_left ((mid_iff hτ).2 h), ite_eq_left h.symm]
  · rw [ite_eq_right (fun hc => h ((mid_iff hτ).1 hc)), ite_eq_right (fun hc => h hc.symm)]

/-! ## 2. `IntegrableAtIndex` — brief 58's input, in this exact shape -/

/-- **Brief 58's obligation.**  Both moments of an increment read at a measurable random index
below the horizon are integrable; brief 58 proves it by domination against
`GaussianMaximal.maxNorm`, whose integrability is report 54's. -/
def IntegrableAtIndex (P : Measure Ω) (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (N : ℕ) : Prop :=
  ∀ f : Ω → ℕ, Measurable f → (∀ ω, f ω < N) →
    Integrable (fun ω => ‖ξ (f ω) ω‖) P ∧ Integrable (fun ω => ‖ξ (f ω) ω‖ ^ 2) P

omit [MeasurableSpace Ω] in
omit [Countable ι] in
/-- `τ` is measurable — it is a stopping time, so `{τ ≤ k}` is measurable for every `k`, and a
`ℕ`-valued map with measurable sublevel sets is measurable. -/
theorem measurable_tau {m0 : MeasurableSpace Ω} (ℱ : Filtration ℕ m0) {η r₀ c₃ : ℝ}
    (hG : ∀ k, MeasurableSet[ℱ k] (stateGood q W A₀ ξ η r₀ c₃ k)) (N : ℕ) :
    Measurable (tau q W A₀ ξ η r₀ c₃ N) := by
  refine measurable_to_countable' fun k => ?_
  have hle : ∀ j, MeasurableSet[m0] {ω | tau q W A₀ ξ η r₀ c₃ N ω ≤ j} := by
    intro j
    have h := isStoppingTime_tau ℱ hG N j
    have h2 : MeasurableSet[ℱ j] {ω | tau q W A₀ ξ η r₀ c₃ N ω ≤ j} := by simpa using h
    exact ℱ.le j _ h2
  have hset : (tau q W A₀ ξ η r₀ c₃ N) ⁻¹' {k}
      = {ω | tau q W A₀ ξ η r₀ c₃ N ω ≤ k} \ {ω | tau q W A₀ ξ η r₀ c₃ N ω ≤ k - 1} ∪
        (if k = 0 then {ω | tau q W A₀ ξ η r₀ c₃ N ω ≤ 0} else ∅) := by
    ext ω
    by_cases hk : k = 0
    · subst hk; simp [Set.mem_preimage]
    · rw [ite_eq_right hk]
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_sdiff,
        Set.mem_ofPred_eq, Set.mem_empty_iff_false, or_false]
      omega
  rw [hset]
  refine MeasurableSet.union ((hle k).diff (hle (k - 1))) ?_
  by_cases hk : k = 0
  · rw [ite_eq_left hk]; exact hle 0
  · rw [ite_eq_right hk]; exact MeasurableSet.empty

omit [MeasurableSpace Ω] in
omit [Countable ι] in
theorem measurable_tau_sub_one {m0 : MeasurableSpace Ω} (ℱ : Filtration ℕ m0) {η r₀ c₃ : ℝ}
    (hG : ∀ k, MeasurableSet[ℱ k] (stateGood q W A₀ ξ η r₀ c₃ k)) (N : ℕ) :
    Measurable (fun ω => tau q W A₀ ξ η r₀ c₃ N ω - 1) :=
  (measurable_tau ℱ hG N).sub_const 1


/-! ## 3. The integral of the stopped error -/

section Integral

variable {P : Measure Ω} [IsProbabilityMeasure P]

omit [Countable ι] [MeasurableSpace Ω] in
/-- **The good-range sum, pointwise.**  The term vanishes off the freeze set, so
`ChainDrift.sum_err_le` bounds it by the freeze count times `ε`. -/
theorem sum_good_le {η r₀ c₃ ε : ℝ} {N m : ℕ} {ω : Ω}
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hε : 0 ≤ ε) (hbd : ∀ k, k < m → ChainWiring.chainErr q W A₀ ξ k ω ≤ ε) :
    ∑ k ∈ Finset.range m,
        (if k + 1 ≤ tau q W A₀ ξ η r₀ c₃ N ω - 1
          then ChainWiring.chainErr q W A₀ ξ k ω else 0)
      ≤ (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) * ε := by
  classical
  refine ChainDrift.sum_err_le (P := fun k => Chain.Freezes q W A₀ ξ k ω)
    (fun k _ hnf => ?_) (fun k hk => ?_) hε ?_
  · rw [ChainWiring.chainErr_eq_zero_of_not_freezes hA₀ hq hne hnf]
    split <;> simp
  · split
    · exact hbd k hk
    · exact hε
  · have h := Chain.card_freezes_le (ξ := ξ) (A₀ := A₀) hA₀ hq hne m ω
    omega

/-- **The stopped error's sum, pointwise**: the freeze count times `ε`, plus one evaluation of the
increment at `τ − 1`. -/
theorem sum_stoppedErr_le {η a₀ r₀ c₃ c ε : ℝ} {N m : ℕ} {ω : Ω} (hN : 1 ≤ N) (hc : 0 ≤ c)
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃) (hlt : r₀ + c₃ * η < a₀)
    (hε : 0 ≤ ε) (hbd : ∀ k, k < m → ChainWiring.chainErr q W A₀ ξ k ω ≤ ε) :
    ∑ k ∈ Finset.range m, stoppedErr q W A₀ ξ η r₀ c₃ c N k ω
      ≤ (finrank ℝ (EuclideanSpace ℝ (UT n)) : ℝ) * ε
        + C₁ n (a₀ - (r₀ + c₃ * η)) c
          * (‖ξ (tau q W A₀ ξ η r₀ c₃ N ω - 1) ω‖
              + ‖ξ (tau q W A₀ ξ η r₀ c₃ N ω - 1) ω‖ ^ 2) := by
  classical
  have hm : 0 < a₀ - (r₀ + c₃ * η) := by linarith
  have hC : 0 ≤ C₁ n (a₀ - (r₀ + c₃ * η)) c := C₁_nonneg hc hm
  have hτ1 : 1 ≤ tau q W A₀ ξ η r₀ c₃ N ω :=
    one_le_tau (q := q) (W := W) (A₀ := A₀) (ξ := ξ) hN hr₀ hc₃ ω
  have hsplit : ∀ k, stoppedErr q W A₀ ξ η r₀ c₃ c N k ω
      ≤ (if k + 1 ≤ tau q W A₀ ξ η r₀ c₃ N ω - 1
          then ChainWiring.chainErr q W A₀ ξ k ω else 0)
        + (if k < tau q W A₀ ξ η r₀ c₃ N ω ∧ ¬ (k + 1 ≤ tau q W A₀ ξ η r₀ c₃ N ω - 1) then
            C₁ n (a₀ - (r₀ + c₃ * η)) c * (‖ξ k ω‖ + ‖ξ k ω‖ ^ 2) else 0) := fun k =>
    stoppedErr_split hN hc hA₀ hq hne hA₀m hη hr₀ hc₃ hlt k ω
  refine le_trans (Finset.sum_le_sum fun k _ => hsplit k) ?_
  rw [Finset.sum_add_distrib]
  refine add_le_add (sum_good_le hA₀ hq hne hε hbd) ?_
  rw [sum_mid_eq (q := q) (W := W) (A₀ := A₀) (ξ := ξ)
    (fun k => C₁ n (a₀ - (r₀ + c₃ * η)) c * (‖ξ k ω‖ + ‖ξ k ω‖ ^ 2)) hτ1]
  split
  · exact le_rfl
  · have : (0 : ℝ) ≤ C₁ n (a₀ - (r₀ + c₃ * η)) c
        * (‖ξ (tau q W A₀ ξ η r₀ c₃ N ω - 1) ω‖
            + ‖ξ (tau q W A₀ ξ η r₀ c₃ N ω - 1) ω‖ ^ 2) := by positivity
    linarith

end Integral


/-! ## 4. The drift side, quantified over the `ChainRaw2` (route change)

Report 56 §2 found `DriftStopped3.DriftSide` **unprovable as stated**: with `α` free,
`Assembly.ChainOutput α g c₀` asks for an ellipsoid of volume `≥ c₀m²κ` avoiding a lattice of
covolume `α^{m+1}p^m`, which Minkowski forbids for all small `α`.  `ChainRaw2.alpha_norm` is what
pins `α`, so the fix is to quantify over the `ChainRaw2` the tail side produces rather than over
`α` and `R`.  It costs nothing: the composition is unchanged, because `DriftSide'` is still a
`∀ Q` statement and `Nonempty` elimination is unaffected. -/

section Sides

open Submission.L10.ConstructionA Submission.L10.Tiling

/-- `DriftStopped3.DriftSide` with the free `α`, `R` replaced by the `ChainRaw2`. -/
def DriftSide' (c₀ : ℝ) : Prop :=
  ∀ m : ℕ, Threshold2.n₁ ≤ m → ∀ (p : ℕ) (Q : ChainRaw2 p (m + 1))
      (g : Fin (m + 1) → ZMod p), g ≠ 0 →
    (∀ y : Fin (m + 1) → ℤ, y ≠ 0 → ‖toE (m + 1) y‖ ≤ Q.R → y ∉ latZ p (m + 1) g) →
    Assembly.ChainOutput Q.alpha g c₀

/-- **The two sides still meet.** -/
theorem chainDelivers_of_sides' {c₀ : ℝ} (htail : PaddedLawSetup.TailSide)
    (hdrift : DriftSide' c₀) : Theorem.ChainDelivers c₀ := by
  intro m hm
  obtain ⟨p, hp, hp0, hQ⟩ := htail m hm
  obtain ⟨Q⟩ := hQ
  exact ⟨p, hp, hp0, Q, fun g hg hfree => hdrift m hm p Q g hg hfree⟩

/-- **`klartag_packing` from the tail side and the corrected drift side**, with `c₀` existentially
produced rather than assumed — report 56 item 4 notes the tree never fixes its value. -/
theorem klartag_packing_of_sides' (htail : PaddedLawSetup.TailSide)
    (hdrift : ∃ c₀ : ℝ, 0 < c₀ ∧ DriftSide' c₀) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      let V := EuclideanSpace ℝ (Fin (n + 1))
      ∃ φ : V →ₗ[ℝ] V, let E := φ '' Metric.ball (0 : V) 1
        (MeasureTheory.volume E : EReal) = c * n ^ 2 ∧
        {v ∈ E | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} := by
  obtain ⟨c₀, hc₀, hd⟩ := hdrift
  exact Theorem.klartag_packing_of_chain hc₀ (chainDelivers_of_sides' htail hd)

end Sides

end Submission.L10.DriftStopped5

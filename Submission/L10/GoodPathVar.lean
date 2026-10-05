import Submission.L10.GoodPathBounds

/-!
# Gate L-10 (`klartag_packing`) — the existence step against a **lower-tail** bound

Brief 94b.  `GoodPathBounds.exists_mem_of_integral_le` shifts Markov by the *worst-case* floor
`L₀ = n·log (mAt n c₃)` (`stoppedLogDet_ge`), which is `≈ −0.07·n`: the ratio is then
`n|log mAt|/(C' + n|log mAt|)`, whose margin decays like `1/n`.  Replacing the floor by a
lower-tail bound at a **constant** depth `t` fixes it.

## The term the plan's formula omits

Markov applied to `(X − L)⁺` needs an upper bound on `E[(X − L)⁺] = (E X − L) + E[(L − X)⁺]`.
The second summand — the **expected shortfall** below `L` — is not `P(X ≤ L)`, and it does not
drop.  Bounding it by the crude floor gives `(L − L₀)·P(X ≤ L) ≈ (v/t²)·0.07·n`, which is linear
in `n` again: measured, the ratio then runs `0.002 06 → 0.294 → 263` at `n₁`, `10¹²`, `10¹⁶` and
the budget fails near `10¹²`.  Bounding it by the **variance** instead is uniform: AM-GM
`u ≤ u²/(2t) + t/2` on `{X ≤ L}` gives

  `E[(L − X)⁺] ≤ v/(2t) + t·P(X ≤ L)/2 = v/t`   at `P(X ≤ L) ≤ v/t²`,

which is `0.13` at `v = 130`, `t = 1000`, and the ratio is then `0.002 012` at **every** `n`.
So `exists_mem_of_variance` takes the shortfall as its hypothesis and
`shortfall_le_of_variance` supplies it from 94a's variance — the tail bound alone is not enough.
-/

set_option linter.unusedSectionVars false

namespace Submission.L10.GoodPathVar

open MeasureTheory Finset

section Var

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- `(x − L)⁺ = (x − L) + (L − x)⁺`. -/
theorem pos_part_split (L x : ℝ) : max (x - L) 0 = (x - L) + max (L - x) 0 := by
  rcases le_total x L with h | h
  · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
  · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring

theorem integrable_pos_part {X : Ω → ℝ} (hX : Integrable X P) (L : ℝ) :
    Integrable (fun ω => max (L - X ω) 0) P :=
  ((integrable_const L).sub hX).pos_part

theorem integrable_pos_part' {X : Ω → ℝ} (hX : Integrable X P) (L : ℝ) :
    Integrable (fun ω => max (X ω - L) 0) P :=
  (hX.sub (integrable_const L)).pos_part

/-- **The existence step against a lower-tail bound.**  `s` is the expected shortfall below `L`
and `f` the good event's failure probability.  Markov runs on `(X − L)⁺`, so nothing here needs a
pointwise floor for `X` — which is the whole point: the floor `n·log (mAt n c₃)` is what made
`GoodPathBounds.exists_mem_of_integral_le`'s margin decay like `1/n`. -/
theorem exists_mem_of_variance {X : Ω → ℝ} (hXm : Measurable X) (hX : Integrable X P)
    {L B b s f : ℝ} (hB : ∫ ω, X ω ∂P ≤ B)
    (hshort : ∫ ω, max (L - X ω) 0 ∂P ≤ s)
    {S : Set Ω} (hS : MeasurableSet S) (hbad : P.real Sᶜ ≤ f) (hLb : L < b)
    (hbudget : (B - L + s) / (b - L) + f < 1) :
    ∃ ω, X ω ≤ b ∧ ω ∈ S := by
  classical
  have hposint := integrable_pos_part' hX L
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := P) (f := fun ω => max (X ω - L) 0)
    (Filter.Eventually.of_forall fun ω => le_max_right _ _) hposint (b - L)
  have hint : ∫ ω, max (X ω - L) 0 ∂P ≤ B - L + s := by
    have heq : ∫ ω, max (X ω - L) 0 ∂P
        = (∫ ω, (X ω - L) ∂P) + ∫ ω, max (L - X ω) 0 ∂P :=
      calc ∫ ω, max (X ω - L) 0 ∂P
          = ∫ ω, ((X ω - L) + max (L - X ω) 0) ∂P :=
            integral_congr_ae (Filter.Eventually.of_forall fun ω => pos_part_split L (X ω))
        _ = (∫ ω, (X ω - L) ∂P) + ∫ ω, max (L - X ω) 0 ∂P :=
            integral_add (hX.sub (integrable_const L)) (integrable_pos_part hX L)
    have hlin : ∫ ω, (X ω - L) ∂P = (∫ ω, X ω ∂P) - L := by
      rw [integral_sub hX (integrable_const L), integral_const]; simp
    rw [heq, hlin]; linarith
  have hsub : {ω | b ≤ X ω} ⊆ {ω | b - L ≤ max (X ω - L) 0} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    exact le_trans (by linarith) (le_max_left _ _)
  have hmono : P.real {ω | b ≤ X ω} ≤ P.real {ω | b - L ≤ max (X ω - L) 0} :=
    measureReal_mono hsub (measure_ne_top P _)
  have hmark : P.real {ω | b ≤ X ω} ≤ (B - L + s) / (b - L) := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith [hmk, hmono, hint]
  have hmeas : MeasurableSet {ω | X ω ≤ b} := measurableSet_le hXm measurable_const
  have hcompl : {ω | X ω ≤ b}ᶜ ⊆ {ω | b ≤ X ω} := by
    intro ω hω
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hω ⊢
    linarith
  have hle : P.real {ω | X ω ≤ b}ᶜ ≤ P.real {ω | b ≤ X ω} :=
    measureReal_mono hcompl (measure_ne_top P _)
  have hG : P.real {ω | X ω ≤ b} + P.real {ω | X ω ≤ b}ᶜ = 1 := by
    rw [measureReal_add_measureReal_compl hmeas]; simp
  have hSsum : P.real S + P.real Sᶜ = 1 := by
    rw [measureReal_add_measureReal_compl hS]; simp
  refine GoodPathBounds.exists_mem_inter_of_one_lt' (P := P) (G := {ω | X ω ≤ b}) hS ?_
  linarith

/-- **The shortfall from the variance.**  AM-GM `u ≤ u²/(2t) + t/2` on `{X ≤ L}`, where
`(L − X)² ≤ (X − E X)²` because `L ≤ E X`.  At `r = v/t²` the bound is `v/t` — a constant, where
the crude floor would give `(L − L₀)·r`, linear in `n`. -/
theorem shortfall_le_of_variance {X : Ω → ℝ} (hXm : Measurable X) (hX : Integrable X P)
    {L v r t : ℝ} (ht : 0 < t) (hmean : L ≤ ∫ ω, X ω ∂P)
    (hsq : Integrable (fun ω => (X ω - ∫ ω, X ω ∂P) ^ 2) P)
    (hvar : ∫ ω, (X ω - ∫ ω, X ω ∂P) ^ 2 ∂P ≤ v)
    (htail : P.real {ω | X ω ≤ L} ≤ r) :
    ∫ ω, max (L - X ω) 0 ∂P ≤ v / (2 * t) + t / 2 * r := by
  classical
  have hmeasS : MeasurableSet {ω | X ω ≤ L} := measurableSet_le hXm measurable_const
  have hind : Integrable
      (fun ω => t / 2 * Set.indicator {ω | X ω ≤ L} (fun _ => (1 : ℝ)) ω) P :=
    ((integrable_const (1 : ℝ)).indicator hmeasS).const_mul _
  have hdom : ∀ ω, max (L - X ω) 0
      ≤ (X ω - ∫ ω, X ω ∂P) ^ 2 / (2 * t)
        + t / 2 * Set.indicator {ω | X ω ≤ L} (fun _ => (1 : ℝ)) ω := by
    intro ω
    rcases le_total (X ω) L with h | h
    · have hmem : ω ∈ {ω | X ω ≤ L} := h
      rw [max_eq_left (by linarith), Set.indicator_of_mem hmem, mul_one, ← sub_nonneg]
      have hsq' : (L - X ω) ^ 2 ≤ (X ω - ∫ ω, X ω ∂P) ^ 2 := by nlinarith
      have key : (X ω - ∫ ω, X ω ∂P) ^ 2 / (2 * t) + t / 2 - (L - X ω)
          = ((X ω - ∫ ω, X ω ∂P) ^ 2 + t ^ 2 - 2 * t * (L - X ω)) / (2 * t) := by
        field_simp
      rw [key]
      refine div_nonneg ?_ (by positivity)
      nlinarith [hsq', sq_nonneg (L - X ω - t)]
    · rw [max_eq_right (by linarith)]
      have h1 : (0 : ℝ) ≤ (X ω - ∫ ω, X ω ∂P) ^ 2 / (2 * t) := by positivity
      have h2 : (0 : ℝ) ≤ t / 2 * Set.indicator {ω | X ω ≤ L} (fun _ => (1 : ℝ)) ω :=
        mul_nonneg (by positivity) (Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
      linarith
  have hgint : Integrable (fun ω => (X ω - ∫ ω, X ω ∂P) ^ 2 / (2 * t)
      + t / 2 * Set.indicator {ω | X ω ≤ L} (fun _ => (1 : ℝ)) ω) P :=
    (hsq.div_const _).add hind
  have hmono := integral_mono (integrable_pos_part hX L) hgint hdom
  calc ∫ ω, max (L - X ω) 0 ∂P
      ≤ ∫ ω, ((X ω - ∫ ω, X ω ∂P) ^ 2 / (2 * t)
          + t / 2 * Set.indicator {ω | X ω ≤ L} (fun _ => (1 : ℝ)) ω) ∂P := hmono
    _ = (∫ ω, (X ω - ∫ ω, X ω ∂P) ^ 2 ∂P) / (2 * t)
          + t / 2 * P.real {ω | X ω ≤ L} := by
        have hii : ∫ ω, Set.indicator {ω | X ω ≤ L} (fun _ => (1 : ℝ)) ω ∂P
            = P.real {ω | X ω ≤ L} := by
          rw [integral_indicator_const (1 : ℝ) hmeasS]; simp
        rw [integral_add (hsq.div_const _) hind, integral_div, integral_const_mul, hii]
    _ ≤ v / (2 * t) + t / 2 * r := by
        have h1 : (∫ ω, (X ω - ∫ ω, X ω ∂P) ^ 2 ∂P) / (2 * t) ≤ v / (2 * t) := by gcongr
        have h2 : t / 2 * P.real {ω | X ω ≤ L} ≤ t / 2 * r :=
          mul_le_mul_of_nonneg_left htail (by positivity)
        linarith

end Var

end Submission.L10.GoodPathVar

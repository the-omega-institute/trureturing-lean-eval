import Submission.L10.ReflStep2
import Submission.L10.ChainDataInst
import Submission.L10.ContactIntegrated

/-!
# Gate L-10 (`klartag_packing`), brief 41 — the second half-law, the count event, and the final
state invariant

Four things, in order.

1. **`map_sum_reflStep`.**  Report 38 §4 left the reflected half-law blocked: `rw` with an equation
   between *named definitions* has to match `StateInvariant.reflStep` inside `Measurable (…)` and
   check a motive, which drags `Submodule.reflection`'s instance argument back in.  The discipline
   of report 38 §3 fixes it — never put the frozen definition on the left of something Lean must
   unfold.  Everything here is proved for `ReflStep2.reflStep2` (or for an explicit lambda), stated
   as a *function-level* equality, and transported by `▸`/`rw` at the top level, where the motive is
   `fun f => Measurable f` and no instance depends on `f`.  With that, `accGood`'s failure bound
   (`hacc`) is a theorem.

2. **The count event.**  Route M (report 38) bounds the accumulated lift by `|C_N| · η`.  `|C_N|`
   is not bounded pathwise, so it is bought with a Markov event
   `countGood c₃ := {ω | |C_N ω| ≤ c₃}` whose failure probability is `(∫ |C_N|)/c₃`, and
   `ChainDataInst.expected_card_le` bounds the integral by `2θ + E = O(1)`.

3. **`wiredGood' := wiredGood ∩ countGood c₃`** and its failure bound.

4. **`stateBounds_wired'`, `hpt_wired'`, `stateInvariant_wired'`** — the invariant with no
   hypotheses beyond the chain's definitions.

`c₃ = n²` is the adopted choice.  At `c₃ = n²` the lift budget is `c₃ · η ≤ √2/n`
(`mul_eta2_le_sq`), the same inequality `ParamsAdopted2.d_mul_eta2_le` already proves for `d`, and
the Markov failure `(2θ+E)/n²` leaves report 25 §3.2's head-room `q·(M'−m₀) < 1` intact by four
orders of magnitude.  `c₃ = n` would need `2θ + E < n/(100 log n) ≈ 5.8` at `n = 4,889`, a bound on
an `O(1)` constant that nothing in the tree supplies.  See the report, §2.
-/

set_option linter.unusedSectionVars false

namespace Submission.L10.StateInvariant4

open MeasureTheory ProbabilityTheory Matrix Finset Module
open scoped ENNReal NNReal RealInnerProductSpace
open Submission.L10 Submission.L10.Increments Submission.L10.StateInvariant
open Submission.L10.StateInvariant2 Submission.L10.StateInvariant3 Submission.L10.ReflStep2

noncomputable section

/-! ## 1. (B2) The reflected half-law, and `hacc` -/

section HalfLaw

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

/-- **The increment law in the tree's own currency.**  Everywhere upstream the step is written
`ξ k = c • ζ k` with `P.map (ζ k) = stdGaussian` (`DischargeGlue`, `StepGlue.coord_law_smul`); this
is the same fact as `P.map (ξ k) = scaled c`, which is what `map_sum_scaled` consumes. -/
theorem map_smul_of_stdGaussian {ζ : Ω → EuclideanSpace ℝ (UT n)} (hζ : Measurable ζ)
    (hlaw : P.map ζ = stdGaussian (EuclideanSpace ℝ (UT n))) (c : ℝ) :
    P.map (fun ω => c • ζ ω) = scaled c (EuclideanSpace ℝ (UT n)) := by
  rw [show (fun ω => c • ζ ω) = (fun x : EuclideanSpace ℝ (UT n) => c • x) ∘ ζ from rfl,
    ← Measure.map_map (by fun_prop) hζ, hlaw, scaled]

/-- The bridge of report 38 §3, at the level of *functions* — this is the form that transports
through `Measurable`, `IndepFun` and `Measure.map` without a motive check on the reflection's
instance argument. -/
theorem reflStep2_eq_fun (k : ℕ) :
    reflStep2 q W A₀ ξ k = StateInvariant.reflStep q W A₀ ξ k :=
  funext fun ω => reflStep2_eq_reflStep k ω

theorem measurable_reflStep2 (hξ : ∀ j, Measurable (ξ j)) (k : ℕ) :
    Measurable (reflStep2 q W A₀ ξ k) := by
  -- The composition is written out in the `have`'s *type*, so `Measurable.comp` is matched
  -- syntactically.  Leaving it to be inferred from the expected type poses `?g ∘ ?f ≟ fun ω => …`,
  -- a higher-order problem that sends the unifier into `Submodule.reflection`'s instance.
  have h : Measurable ((fun p : (ℕ → EuclideanSpace ℝ (UT n)) × EuclideanSpace ℝ (UT n) =>
        reflOf q (chainU q W A₀ k p.1).2 p.2) ∘ (fun ω : Ω => (past ξ k ω, ξ k ω))) :=
    Measurable.comp (measurable_U_uncurry (q := q) (W := W) (A₀ := A₀) k)
      (Measurable.prodMk (measurable_past (ξ := ξ) hξ k) (hξ k))
  exact h

/-- **The reflected increment is measurable.** -/
theorem measurable_reflStep (hξ : ∀ j, Measurable (ξ j)) (k : ℕ) :
    Measurable (StateInvariant.reflStep q W A₀ ξ k) := by
  have h := measurable_reflStep2 (q := q) (W := W) (A₀ := A₀) hξ k
  rwa [reflStep2_eq_fun] at h

/-- The partial sum of reflected increments, read as a function of the past sequence. -/
def reflSumPast (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι)
    (A₀ : EuclideanSpace ℝ (UT n)) (k : ℕ) (v : ℕ → EuclideanSpace ℝ (UT n)) :
    EuclideanSpace ℝ (UT n) :=
  ∑ j ∈ Finset.range k, reflOf q (chainU q W A₀ j v).2 (v j)

theorem measurable_reflSumPast (k : ℕ) : Measurable (reflSumPast q W A₀ k) := by
  show Measurable fun v : ℕ → EuclideanSpace ℝ (UT n) =>
    ∑ j ∈ Finset.range k, reflOf q (chainU q W A₀ j v).2 (v j)
  refine Finset.measurable_sum _ fun j _ => ?_
  have h : Measurable ((fun p : (ℕ → EuclideanSpace ℝ (UT n)) × EuclideanSpace ℝ (UT n) =>
        reflOf q (chainU q W A₀ j p.1).2 p.2)
      ∘ (fun v : ℕ → EuclideanSpace ℝ (UT n) => (v, v j))) :=
    Measurable.comp (measurable_U_uncurry (q := q) (W := W) (A₀ := A₀) j)
      (Measurable.prodMk measurable_id (measurable_pi_apply j))
  exact h

theorem reflSumPast_past (k : ℕ) (ω : Ω) :
    reflSumPast q W A₀ k (past ξ k ω)
      = ∑ j ∈ Finset.range k, StateInvariant.reflStep q W A₀ ξ j ω :=
  Finset.sum_congr rfl fun _j hj => reflOf_past_eq_reflStep (Finset.mem_range.1 hj) ω

/-- **The per-step law of the reflected increment**: the frozen rotation preserves `N(0, c²·Id)`. -/
theorem map_reflStep {c : ℝ} (hξ : ∀ j, Measurable (ξ j)) (hindep : iIndepFun ξ P)
    (hlaw : ∀ j, P.map (ξ j) = scaled c (EuclideanSpace ℝ (UT n))) (k : ℕ) :
    P.map (StateInvariant.reflStep q W A₀ ξ k) = scaled c (EuclideanSpace ℝ (UT n)) := by
  have h1 : P.map (reflStep2 q W A₀ ξ k) = scaled c (EuclideanSpace ℝ (UT n)) :=
    map_frozen_isometry_scaled (measurable_past hξ k) (hξ k)
      (indepFun_past hξ hindep k) (hlaw k)
      (fun v => reflOf q (chainU q W A₀ k v).2) (measurable_U_uncurry k)
  rwa [reflStep2_eq_fun] at h1

/-- **…and it stays independent of the partial sum before it.**  The partial sum is
`reflSumPast ∘ past`, a measurable function of the past, so `IndepFun.comp` applies. -/
theorem indepFun_sum_reflStep {c : ℝ} (hξ : ∀ j, Measurable (ξ j)) (hindep : iIndepFun ξ P)
    (hlaw : ∀ j, P.map (ξ j) = scaled c (EuclideanSpace ℝ (UT n))) (k : ℕ) :
    IndepFun (fun ω => ∑ j ∈ Finset.range k, StateInvariant.reflStep q W A₀ ξ j ω)
      (StateInvariant.reflStep q W A₀ ξ k) P := by
  have h1 : IndepFun (past ξ k) (reflStep2 q W A₀ ξ k) P :=
    indepFun_frozen_isometry_scaled (measurable_past hξ k) (hξ k)
      (indepFun_past hξ hindep k) (hlaw k)
      (fun v => reflOf q (chainU q W A₀ k v).2) (measurable_U_uncurry k)
  have h2 := h1.comp (measurable_reflSumPast (q := q) (W := W) (A₀ := A₀) k) measurable_id
  have e1 : (reflSumPast q W A₀ k ∘ past ξ k)
      = fun ω => ∑ j ∈ Finset.range k, StateInvariant.reflStep q W A₀ ξ j ω :=
    funext fun ω => reflSumPast_past k ω
  have e2 : (id ∘ reflStep2 q W A₀ ξ k) = StateInvariant.reflStep q W A₀ ξ k :=
    reflStep2_eq_fun k
  rw [e1, e2] at h2
  exact h2

/-- **(B2) The second half-law** — `Σ_{j<k} R_j ξ_j ~ N(0, k c² · Id)`.  This is what report 38 §4
named as the missing piece. -/
theorem map_sum_reflStep {c : ℝ} (hc : 0 ≤ c) (hξ : ∀ j, Measurable (ξ j))
    (hindep : iIndepFun ξ P) (hlaw : ∀ j, P.map (ξ j) = scaled c (EuclideanSpace ℝ (UT n)))
    (k : ℕ) :
    P.map (fun ω => ∑ j ∈ Finset.range k, StateInvariant.reflStep q W A₀ ξ j ω)
      = scaled (Real.sqrt k * c) (EuclideanSpace ℝ (UT n)) :=
  map_sum_scaled hc (fun j => measurable_reflStep hξ j) (fun j => map_reflStep hξ hindep hlaw j)
    (fun m => indepFun_sum_reflStep hξ hindep hlaw m) k

/-- **`hacc`: the failure probability of the accumulated event**, with both half-laws supplied.
The frozen `StateInvariant.measureReal_compl_accGood_le` wants `0 < ρ k` for every `k`, which
`ρ k = √k·c` fails at `k = 0`; the `k = 0` term of the union bound is vacuous anyway
(`gaussSum … 0 ω = 0 ≤ r₀`), so the union runs over `Ico 1 N` here. -/
theorem measureReal_compl_accGood_le' {N : ℕ} {c r₀ s : ℝ} (hc : 0 < c) (hr₀ : 0 ≤ r₀)
    (hs : 1 ≤ s) (hξm : ∀ k, Measurable (ξ k)) (hindep : iIndepFun ξ P)
    (hlaw : ∀ j, P.map (ξ j) = scaled c (EuclideanSpace ℝ (UT n)))
    (hthr : 6 * (Real.sqrt N * c) * s * Real.sqrt n ≤ r₀) :
    P.real (accGood q W A₀ ξ N r₀)ᶜ ≤ (N : ℝ) * (2 * (4 * Real.exp (-(s ^ 2 * n)))) := by
  classical
  set cc : ℝ := 4 * Real.exp (-(s ^ 2 * n)) with hcc
  have hs0 : (0 : ℝ) ≤ s := le_trans zero_le_one hs
  have hfac : (0 : ℝ) ≤ 6 * c * s * Real.sqrt n :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hc.le) hs0) (Real.sqrt_nonneg _)
  have hthr_k : ∀ k, k ≤ N → 6 * (Real.sqrt k * c) * s * Real.sqrt n ≤ r₀ := by
    intro k hk
    calc 6 * (Real.sqrt k * c) * s * Real.sqrt n
        = Real.sqrt k * (6 * c * s * Real.sqrt n) := by ring
      _ ≤ Real.sqrt N * (6 * c * s * Real.sqrt n) :=
          mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by exact_mod_cast hk)) hfac
      _ = 6 * (Real.sqrt N * c) * s * Real.sqrt n := by ring
      _ ≤ r₀ := hthr
  have hξlaw : ∀ k, P.map (fun ω => ∑ j ∈ Finset.range k, ξ j ω)
      = scaled (Real.sqrt k * c) (EuclideanSpace ℝ (UT n)) :=
    fun k => map_sum_xi hc.le hξm hindep hlaw k
  have hrlaw : ∀ k, P.map (fun ω => ∑ j ∈ Finset.range k, StateInvariant.reflStep q W A₀ ξ j ω)
      = scaled (Real.sqrt k * c) (EuclideanSpace ℝ (UT n)) :=
    fun k => map_sum_reflStep hc.le hξm hindep hlaw k
  have hsub : (accGood q W A₀ ξ N r₀)ᶜ ⊆ ⋃ k ∈ Finset.Ico 1 N,
      ({ω | 6 * (Real.sqrt k * c) * s * Real.sqrt n ≤
          ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat (∑ j ∈ Finset.range k, ξ j ω))‖}
        ∪ {ω | 6 * (Real.sqrt k * c) * s * Real.sqrt n ≤
          ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
            (symMat (∑ j ∈ Finset.range k, StateInvariant.reflStep q W A₀ ξ j ω))‖}) := by
    intro ω hω
    simp only [accGood, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_le] at hω
    obtain ⟨k, hk, hlt⟩ := hω
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · exfalso
        subst hk0
        have hz : StateInvariant.gaussSum q W A₀ ξ 0 ω = 0 := by
          simp [StateInvariant.gaussSum]
        rw [hz, symMat_zero, map_zero, norm_zero] at hlt
        linarith
      · exact hk0
    refine Set.mem_biUnion (Finset.mem_Ico.2 ⟨hk1, hk⟩) ?_
    by_contra hcon
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hcon
    have hb := opNorm_gaussSum_le (q := q) (W := W) (A₀ := A₀) (ξ := ξ) k ω
    have h1 := hthr_k k (le_of_lt hk)
    linarith [hcon.1, hcon.2, hb, hlt]
  have hcard : ((Finset.Ico 1 N).card : ℝ) ≤ (N : ℝ) := by
    rw [Nat.card_Ico]
    exact_mod_cast Nat.sub_le N 1
  have hcc0 : (0 : ℝ) ≤ 2 * cc := by
    have : (0 : ℝ) < Real.exp (-(s ^ 2 * n)) := Real.exp_pos _
    rw [hcc]; linarith
  calc P.real (accGood q W A₀ ξ N r₀)ᶜ
      ≤ P.real (⋃ k ∈ Finset.Ico 1 N, _) := measureReal_mono hsub (measure_ne_top P _)
    _ ≤ ∑ k ∈ Finset.Ico 1 N, P.real
          ({ω | 6 * (Real.sqrt k * c) * s * Real.sqrt n ≤
            ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (symMat (∑ j ∈ Finset.range k, ξ j ω))‖}
          ∪ {ω | 6 * (Real.sqrt k * c) * s * Real.sqrt n ≤
            ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
              (symMat (∑ j ∈ Finset.range k,
                StateInvariant.reflStep q W A₀ ξ j ω))‖}) :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _k ∈ Finset.Ico 1 N, (2 * cc) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk1 : 1 ≤ k := (Finset.mem_Ico.1 hk).1
        have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
        have hρ : 0 < Real.sqrt k * c := mul_pos (Real.sqrt_pos.2 hkR) hc
        refine (measureReal_union_le _ _).trans ?_
        have hA := measureReal_opNorm_symMat_ge hρ
          (Finset.measurable_sum _ fun j _ => hξm j) (hξlaw k) s hs
        have hB := measureReal_opNorm_symMat_ge hρ
          (Finset.measurable_sum _ fun j _ => measurable_reflStep hξm j) (hrlaw k) s hs
        rw [hcc]; linarith
    _ = ((Finset.Ico 1 N).card : ℝ) * (2 * cc) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) * (2 * cc) := mul_le_mul_of_nonneg_right hcard hcc0

end HalfLaw

/-! ## 2. The count event `{|C_N| ≤ c₃}` -/

section Count

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

/-- **The count event.**  Route M's lift bound is `|C_k| · η`; this is the event that buys `|C_N|`,
and `Chain.chain_snd_mono` makes the terminal count dominate every earlier one. -/
def countGood (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι) (A₀ : EuclideanSpace ℝ (UT n))
    (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (N : ℕ) (c₃ : ℝ) : Set Ω :=
  {ω | ((Chain.chain q W A₀ ξ N ω).2.card : ℝ) ≤ c₃}

/-- The contact set only grows, so one bound at `N` bounds every `k ≤ N`. -/
theorem card_le_of_countGood {N : ℕ} {c₃ : ℝ} {ω : Ω}
    (hω : ω ∈ countGood q W A₀ ξ N c₃) {k : ℕ} (hk : k ≤ N) :
    ((Chain.chain q W A₀ ξ k ω).2.card : ℝ) ≤ c₃ := by
  refine le_trans ?_ hω
  exact_mod_cast Finset.card_le_card (Chain.chain_snd_mono hk ω)

theorem card_eq_sum_indicator (N : ℕ) (ω : Ω) :
    ((Chain.chain q W A₀ ξ N ω).2.card : ℝ)
      = ∑ i ∈ W, Set.indicator {ω | i ∈ (Chain.chain q W A₀ ξ N ω).2} (fun _ => (1 : ℝ)) ω := by
  classical
  have hfil : W.filter (fun i => i ∈ (Chain.chain q W A₀ ξ N ω).2)
      = (Chain.chain q W A₀ ξ N ω).2 := by
    ext i
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Chain.chain_snd_subset_window N ω h, h⟩⟩
  rw [← hfil, Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i ∈ (Chain.chain q W A₀ ξ N ω).2 <;> simp [Set.indicator, hi]

theorem measurable_card_chain (hξ : ∀ k, Measurable (ξ k)) (N : ℕ) :
    Measurable fun ω => ((Chain.chain q W A₀ ξ N ω).2.card : ℝ) := by
  classical
  simp only [card_eq_sum_indicator]
  refine Finset.measurable_sum _ fun i _ => ?_
  exact (measurable_const : Measurable fun _ : Ω => (1 : ℝ)).indicator
    (Chain.measurableSet_mem_active hξ N i)

theorem integrable_card_chain (hξ : ∀ k, Measurable (ξ k)) (N : ℕ) :
    Integrable (fun ω => ((Chain.chain q W A₀ ξ N ω).2.card : ℝ)) P := by
  classical
  have hint : ∀ i ∈ W, Integrable
      (fun ω => Set.indicator {ω | i ∈ (Chain.chain q W A₀ ξ N ω).2} (fun _ => (1 : ℝ)) ω) P :=
    fun i _ => (integrable_const (1 : ℝ)).indicator (Chain.measurableSet_mem_active hξ N i)
  have h := integrable_finsetSum (μ := P) W hint
  simpa only [← card_eq_sum_indicator] using h

/-- **Markov.**  The count event fails with probability at most `(∫ |C_N|)/c₃`. -/
theorem measureReal_compl_countGood_le (hξ : ∀ k, Measurable (ξ k)) {N : ℕ} {c₃ : ℝ}
    (hc₃ : 0 < c₃) :
    P.real (countGood q W A₀ ξ N c₃)ᶜ
      ≤ (∫ ω, ((Chain.chain q W A₀ ξ N ω).2.card : ℝ) ∂P) / c₃ := by
  classical
  have hnn : (0 : ℝ → ℝ) = 0 := rfl
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := P)
    (f := fun ω => ((Chain.chain q W A₀ ξ N ω).2.card : ℝ))
    (Filter.Eventually.of_forall fun ω => Nat.cast_nonneg _)
    (integrable_card_chain hξ N) c₃
  have hsub : (countGood q W A₀ ξ N c₃)ᶜ
      ⊆ {ω | c₃ ≤ ((Chain.chain q W A₀ ξ N ω).2.card : ℝ)} := by
    intro ω hω
    simp only [countGood, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hω
    exact le_of_lt hω
  have hmono : P.real (countGood q W A₀ ξ N c₃)ᶜ
      ≤ P.real {ω | c₃ ≤ ((Chain.chain q W A₀ ξ N ω).2.card : ℝ)} :=
    measureReal_mono hsub (measure_ne_top P _)
  rw [le_div_iff₀ hc₃, mul_comm]
  calc c₃ * P.real (countGood q W A₀ ξ N c₃)ᶜ
      ≤ c₃ * P.real {ω | c₃ ≤ ((Chain.chain q W A₀ ξ N ω).2.card : ℝ)} :=
        mul_le_mul_of_nonneg_left hmono hc₃.le
    _ ≤ ∫ ω, ((Chain.chain q W A₀ ξ N ω).2.card : ℝ) ∂P := hmk

/-- **The count event's failure bound, with `ChainDataInst.expected_card_le` supplying the
integral.**  `2θ + E` is report 7 §8's `4K + C·e^{−cn}`, an `O(1)` constant. -/
theorem measureReal_compl_countGood_le_expected (hξ : ∀ k, Measurable (ξ k)) {N : ℕ} {c₃ : ℝ}
    (hc₃ : 0 < c₃) (weight err : ι → ℝ)
    (htail : ∀ i ∈ W, P.real {ω | i ∈ (Chain.chain q W A₀ ξ N ω).2} ≤ 2 * weight i + err i)
    {θ E : ℝ} (hθ : ∑ i ∈ W, weight i ≤ θ) (hE : ∑ i ∈ W, err i ≤ E) :
    P.real (countGood q W A₀ ξ N c₃)ᶜ ≤ (2 * θ + E) / c₃ := by
  refine le_trans (measureReal_compl_countGood_le hξ hc₃) ?_
  refine div_le_div_of_nonneg_right ?_ hc₃.le
  exact ChainDataInst.expected_card_le P W (fun ω => (Chain.chain q W A₀ ξ N ω).2)
    (fun ω => Chain.chain_snd_subset_window N ω)
    (fun i _ => Chain.measurableSet_mem_active hξ N i) weight err htail hθ hE

end Count

/-! ## 3. `wiredGood'` and its failure bound -/

section Wired

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

/-- **The event the chain is run on, final form**: report 12's accumulated bound, report 15's
per-step bound, report 29's `N` partial sums, and Route M's contact count. -/
def wiredGood' (r : ℝ) (Wacc : Ω → EuclideanSpace ℝ (UT n))
    (ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)) (thr : ℝ) (N : ℕ) (η : ℝ)
    (q : ι → EuclideanSpace ℝ (UT n)) (W : Finset ι) (A₀ : EuclideanSpace ℝ (UT n))
    (r₀ c₃ : ℝ) : Set Ω :=
  wiredGood r Wacc ξ thr N η q W A₀ r₀ ∩ countGood q W A₀ ξ N c₃

theorem wiredGood'_subset {r : ℝ} {Wacc : Ω → EuclideanSpace ℝ (UT n)} {thr : ℝ} {N : ℕ}
    {η r₀ c₃ : ℝ} :
    wiredGood' r Wacc ξ thr N η q W A₀ r₀ c₃ ⊆ wiredGood r Wacc ξ thr N η q W A₀ r₀ :=
  Set.inter_subset_left

/-- **The four failure probabilities add.** -/
theorem measureReal_compl_wiredGood'_le (r : ℝ) (Wacc : Ω → EuclideanSpace ℝ (UT n)) (thr : ℝ)
    (N : ℕ) (η r₀ c₃ : ℝ) :
    P.real (wiredGood' r Wacc ξ thr N η q W A₀ r₀ c₃)ᶜ
      ≤ P.real (StepGlue.chainGood r Wacc ξ thr N η)ᶜ
        + P.real (accGood q W A₀ ξ N r₀)ᶜ
        + P.real (countGood q W A₀ ξ N c₃)ᶜ := by
  have hset : (wiredGood' r Wacc ξ thr N η q W A₀ r₀ c₃)ᶜ
      = (wiredGood r Wacc ξ thr N η q W A₀ r₀)ᶜ ∪ (countGood q W A₀ ξ N c₃)ᶜ := by
    rw [wiredGood', Set.compl_inter]
  rw [hset]
  refine (measureReal_union_le _ _).trans ?_
  have hbase := measureReal_compl_wiredGood_le (P := P) (q := q) (W := W) (A₀ := A₀) (ξ := ξ)
    r Wacc thr N η r₀
  linarith

end Wired

/-! ## 4. The state invariant, with `cV` gone and `hcard` discharged -/

section Assembly

variable {n : ℕ} {ι : Type*} [DecidableEq ι] [Countable ι] {Ω : Type*} [MeasurableSpace Ω]
variable {q : ι → EuclideanSpace ℝ (UT n)} {W : Finset ι} {A₀ : EuclideanSpace ℝ (UT n)}
  {ξ : ℕ → Ω → EuclideanSpace ℝ (UT n)}

/-- **`StateBounds` on `wiredGood'`, with no hypotheses beyond the chain's definitions.**  Route M
gives `‖liftSum k‖ ≤ |C_k|·η`; `countGood` gives `|C_k| ≤ c₃`. -/
theorem stateBounds_wired' {r : ℝ} {Wacc : Ω → EuclideanSpace ℝ (UT n)} {thr : ℝ} {N : ℕ}
    {η a₀ r₀ c₃ : ℝ}
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃)
    (hlt : r₀ + c₃ * η < a₀) :
    ∀ k, k < N → ∀ ω ∈ wiredGood' r Wacc ξ thr N η q W A₀ r₀ c₃,
      Discharge.StateBounds (symMat (Chain.chain q W A₀ ξ k ω).1)
        (a₀ - (r₀ + c₃ * η)) (a₀ + (r₀ + c₃ * η)) := by
  intro k hk ω hω
  have hstep : ∀ j, j < k → ‖gaussStep q W A₀ ξ j ω‖ ≤ η := fun j hj =>
    le_trans (Submodule.norm_starProjection_apply_le _ _) (hω.1.1.2 j (lt_trans hj hk))
  have hlift : ‖liftSum q W A₀ ξ k ω‖ ≤ c₃ * η := by
    refine le_trans (LiftBound.norm_liftSum_le_card hA₀ hq hne hη k ω hstep) ?_
    exact mul_le_mul_of_nonneg_right (card_le_of_countGood hω.2 (le_of_lt hk)) hη
  exact LiftBound.stateBounds_of_chain_count hA₀ hq hne hA₀m hr₀ (by positivity)
    (hω.1.2 k hk) hlift hlt

/-- **`hpt` on `wiredGood'`** — the last hypothesis of `StepInputs2.driftInputs_step_chain`, with
the state invariant discharged and no `cV`. -/
theorem hpt_wired' {r : ℝ} {Wacc : Ω → EuclideanSpace ℝ (UT n)} {thr : ℝ} {N : ℕ}
    {η a₀ r₀ c₃ δ : ℝ}
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃)
    (hlt : r₀ + c₃ * η < a₀)
    (hδ : η / (a₀ - (r₀ + c₃ * η)) ≤ δ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    ∀ k, k < N → ∀ ω ∈ wiredGood' r Wacc ξ thr N η q W A₀ r₀ c₃,
      ChainWiring.logDet (Chain.chain q W A₀ ξ (k + 1) ω).1
        ≤ ChainWiring.logDet (Chain.chain q W A₀ ξ k ω).1
          + ⟪(Chain.freeSub q (Chain.chain q W A₀ ξ k ω).2).starProjection
              (Discharge.matToUT (symMat (Chain.chain q W A₀ ξ k ω).1)⁻¹), ξ k ω⟫
          - (1 / (2 * (a₀ + (r₀ + c₃ * η)) ^ 2 * (1 + δ) ^ 2))
            * ‖(Chain.freeSub q (Chain.chain q W A₀ ξ k ω).2).starProjection (ξ k ω)‖ ^ 2
          + ChainWiring.chainErr q W A₀ ξ k ω := by
  intro k hk ω hω
  exact Discharge.hpt_step
    (stateBounds_wired' hA₀ hq hne hA₀m hη hr₀ hc₃ hlt k hk ω hω)
    (StepInputs2.opNorm_step_le_of_stepGood hω.1.1.2 hk _) hδ hδ0 hδ1

/-- **`DischargeGlue.StateInvariant` itself**, for a successor whose `chainGood` parameters already
force the accumulated bound and the contact count.  When the successor's event is `wiredGood'`,
`hsub` is `Set.inter_subset_right` twice. -/
theorem stateInvariant_wired' {r : ℝ} {Wacc : Ω → EuclideanSpace ℝ (UT n)} {thr : ℝ} {N : ℕ}
    {η a₀ r₀ c₃ : ℝ}
    (hA₀ : A₀ ∈ Chain.kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (hA₀m : symMat A₀ = a₀ • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hη : 0 ≤ η) (hr₀ : 0 ≤ r₀) (hc₃ : 0 ≤ c₃)
    (hacc : StepGlue.chainGood r Wacc ξ thr N η ⊆ accGood q W A₀ ξ N r₀)
    (hcnt : StepGlue.chainGood r Wacc ξ thr N η ⊆ countGood q W A₀ ξ N c₃)
    (hlt : r₀ + c₃ * η < a₀) :
    DischargeGlue.StateInvariant q W A₀ ξ r Wacc thr N η
      (a₀ - (r₀ + c₃ * η)) (a₀ + (r₀ + c₃ * η)) := by
  intro k hk ω hω
  exact stateBounds_wired' hA₀ hq hne hA₀m hη hr₀ hc₃ hlt k hk ω
    ⟨⟨hω, hacc hω⟩, hcnt hω⟩

end Assembly

/-! ## 5. The numeric side: `c₃ = n²` fits the lift budget -/

section Numeric

/-- **The lift budget at `c₃ = n²`**: `c₃ · η ≤ √2/n`, the same inequality
`ParamsAdopted2.d_mul_eta2_le` proves for the dimension `d`, so the threshold does not move. -/
theorem mul_eta2_le_sq {n : ℕ} (hn : 3 ≤ n) :
    (n : ℝ) ^ 2
        * Real.sqrt (2 * ParamsAdopted2.stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ) * (n : ℝ))
      ≤ Real.sqrt 2 / (n : ℝ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by
    have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have he := ParamsAdopted2.eta2_le hn
  have he0 : (0 : ℝ) ≤ Real.sqrt
      (2 * ParamsAdopted2.stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ) * (n : ℝ)) :=
    Real.sqrt_nonneg _
  calc (n : ℝ) ^ 2
        * Real.sqrt (2 * ParamsAdopted2.stepSizeAdopted2 n * (Fintype.card (UT n) : ℝ) * (n : ℝ))
      ≤ (n : ℝ) ^ 2 * (Real.sqrt 2 / (n : ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_left he (by positivity)
    _ = Real.sqrt 2 / (n : ℝ) := by field_simp

end Numeric

end

end Submission.L10.StateInvariant4

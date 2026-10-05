/-
Gate L-10 (`klartag_packing`), brief 8.

**The padding construction and conditional symmetry (`hsym`)**, discharging the second named input
of `PaddedTail.padded_increment_tail`.

The chain's increments `d_k = ⟨ξ_k, π_k(x⊗x)⟩` are conditionally Gaussian of *variable* variance
`σ_k² = h·|π_k(x⊗x)|² ≤ h·|x|⁴ = δ`.  Pad with an independent `c_k·η_k`, `c_k = √(δ − σ_k²)`, so
that the padded increments are i.i.d. `N(0,δ)`.  Write `S̃_k = (M_k − M₀) + P_k` with
`P_k = ∑_{i<k} c_i η_i` the accumulated padding.

Report 2 priced `hsym` at ≈ 200 lines via a conditional-symmetry argument at the first passage
time.  As with `hlevy`, no conditioning is needed: on the product space `Ω₁ × (Fin N → ℝ)` (chain ×
padding) the map `negPad` that negates *every* padding coordinate is measure preserving, fixes the
hitting event (which depends only on the chain), and negates `P_k`.  `LevyMaximal`'s
`measure_le_two_mul_of_reflection_family` then applies verbatim.

Note what is **not** used: no Gaussian-ness of the padding, only that its law is symmetric; and no
conditional law for the chain's increments at all.  `hsym` holds for an arbitrary adapted chain.
-/
import Submission.L10.LevyMaximal

namespace Submission.L10

open MeasureTheory Set Finset
open scoped ENNReal NNReal

section Padding

variable {Ω₁ : Type*} [MeasurableSpace Ω₁] {N : ℕ}

/-! ## 1. The padded process -/

/-- The accumulated padding `P_k = ∑_{i<k} c_i(ω₁)·η_i`. -/
def padSum (c : ℕ → Ω₁ → ℝ) (k : ℕ) (ω : Ω₁ × (Fin N → ℝ)) : ℝ :=
  ∑ i : Fin N, if (i : ℕ) < k then c i ω.1 * ω.2 i else 0

/-- The padded process `S̃_k = (M_k − M₀) + P_k`. -/
def paddedProc (M : ℕ → Ω₁ → ℝ) (M₀ : ℝ) (c : ℕ → Ω₁ → ℝ) (k : ℕ)
    (ω : Ω₁ × (Fin N → ℝ)) : ℝ := (M k ω.1 - M₀) + padSum c k ω

/-- Negate every padding coordinate, leaving the chain alone. -/
def negPad (N : ℕ) : Ω₁ × (Fin N → ℝ) → Ω₁ × (Fin N → ℝ) :=
  Prod.map id (flipTail N 0)

theorem flipTail_zero_apply (N : ℕ) (ω : Fin N → ℝ) (i : Fin N) :
    flipTail N 0 ω i = -(ω i) := by
  simp [flipTail, flipCoords]

omit [MeasurableSpace Ω₁] in
theorem negPad_fst [MeasurableSpace Ω₁] (N : ℕ) (ω : Ω₁ × (Fin N → ℝ)) :
    (negPad N ω).1 = ω.1 := rfl

omit [MeasurableSpace Ω₁] in
theorem negPad_snd [MeasurableSpace Ω₁] (N : ℕ) (ω : Ω₁ × (Fin N → ℝ)) (i : Fin N) :
    (negPad N ω).2 i = -(ω.2 i) := flipTail_zero_apply N ω.2 i

/-- The accumulated padding is odd in the padding coordinates. -/
theorem padSum_negPad (c : ℕ → Ω₁ → ℝ) (k : ℕ) (ω : Ω₁ × (Fin N → ℝ)) :
    padSum c k (negPad N ω) = -(padSum c k ω) := by
  have key : padSum c k (negPad N ω)
      = ∑ i : Fin N, -(if (i : ℕ) < k then c i ω.1 * ω.2 i else 0) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases h : (i : ℕ) < k
    · simp [h, negPad_fst, negPad_snd]
    · simp [h]
  rw [key]
  simp [padSum]

/-- `negPad` is measure preserving when the padding law is symmetric. -/
theorem measurePreserving_negPad {P₁ : Measure Ω₁} {ν : Measure ℝ}
    [SFinite P₁] [IsProbabilityMeasure ν]
    (hν : MeasurePreserving (fun x : ℝ => -x) ν ν) (N : ℕ) :
    MeasurePreserving (negPad (Ω₁ := Ω₁) N)
      (P₁.prod (Measure.pi fun _ : Fin N => ν)) (P₁.prod (Measure.pi fun _ : Fin N => ν)) :=
  (MeasurePreserving.id P₁).prod (measurePreserving_flipCoords hν _)

/-! ## 2. Measurability -/

theorem measurable_padSum {c : ℕ → Ω₁ → ℝ} (hc : ∀ i, Measurable (c i)) (k : ℕ) :
    Measurable (padSum (N := N) c k) := by
  unfold padSum
  refine Finset.measurable_sum _ (fun i _ => ?_)
  by_cases h : (i : ℕ) < k
  · simp only [h, ite_true]
    exact ((hc i).comp measurable_fst).mul (((measurable_pi_apply i)).comp measurable_snd)
  · simp only [h, ite_false]
    exact measurable_const

/-! ## 3. The hitting events -/

/-- `{∃ k ≤ N, M_k ≤ 0}` — the chain reaches the boundary. Depends only on the chain. -/
def hitSet (M : ℕ → Ω₁ → ℝ) (N : ℕ) : Set (Ω₁ × (Fin N → ℝ)) := {ω | ∃ k ≤ N, M k ω.1 ≤ 0}

/-- `{∃ k ≤ N, S̃_k ≤ −M₀}` — the padded process reaches `−M₀`. -/
def levSet (M : ℕ → Ω₁ → ℝ) (M₀ : ℝ) (c : ℕ → Ω₁ → ℝ) (N : ℕ) : Set (Ω₁ × (Fin N → ℝ)) :=
  {ω | ∃ k ≤ N, paddedProc M M₀ c k ω ≤ -M₀}

/-- **`hsym`: the padded process reaches `−M₀` with at least half the probability that the chain
reaches the boundary.**

`P(∃ k ≤ N, M_k ≤ 0) ≤ 2 · P(∃ k ≤ N, S̃_k ≤ −M₀)`.

This is the first of the two factors of 2 in `padded_increment_tail`'s constant 4.  It needs only
that the padding law is symmetric; the chain `M` is completely arbitrary. -/
theorem hsym_of_symmetric {P₁ : Measure Ω₁} {ν : Measure ℝ}
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure ν]
    (hν : MeasurePreserving (fun x : ℝ => -x) ν ν)
    {M c : ℕ → Ω₁ → ℝ} (hM : ∀ k, Measurable (M k)) (hc : ∀ i, Measurable (c i))
    (M₀ : ℝ) (N : ℕ) :
    (P₁.prod (Measure.pi fun _ : Fin N => ν)) (hitSet M N)
      ≤ 2 * (P₁.prod (Measure.pi fun _ : Fin N => ν)) (levSet M M₀ c N) := by
  classical
  set P : Measure (Ω₁ × (Fin N → ℝ)) := P₁.prod (Measure.pi fun _ : Fin N => ν) with hP
  set E : ℕ → Set (Ω₁ × (Fin N → ℝ)) :=
    fun k => {ω | M k ω.1 ≤ 0 ∧ ∀ j < k, ¬ (M j ω.1 ≤ 0)} with hE
  set F : ℕ → Set (Ω₁ × (Fin N → ℝ)) := fun k => {ω | padSum c k ω ≤ 0} with hF
  set G : ℕ → Set (Ω₁ × (Fin N → ℝ)) := fun k => {ω | 0 ≤ padSum c k ω} with hG
  -- measurability
  have hMm : ∀ k : ℕ, MeasurableSet {ω : Ω₁ × (Fin N → ℝ) | M k ω.1 ≤ 0} := fun k =>
    measurableSet_le ((hM k).comp measurable_fst) measurable_const
  have hEm : ∀ k : ℕ, MeasurableSet (E k) := by
    intro k
    have h2 : MeasurableSet
        (⋂ j ∈ Finset.range k, {ω : Ω₁ × (Fin N → ℝ) | ¬ (M j ω.1 ≤ 0)}) :=
      MeasurableSet.biInter (Finset.range k).countable_toSet (fun j _ => (hMm j).compl)
    have heq : E k = {ω : Ω₁ × (Fin N → ℝ) | M k ω.1 ≤ 0}
        ∩ ⋂ j ∈ Finset.range k, {ω : Ω₁ × (Fin N → ℝ) | ¬ (M j ω.1 ≤ 0)} := by
      ext ω
      simp [hE, Finset.mem_range]
    rw [heq]
    exact (hMm k).inter h2
  have hFm : ∀ k : ℕ, MeasurableSet (F k) := fun k =>
    measurableSet_le (measurable_padSum hc k) measurable_const
  -- disjointness
  have hdisj : ∀ j k : ℕ, j ≠ k → Disjoint (E j) (E k) := by
    intro j k hjk
    rw [Set.disjoint_left]
    intro ω hj hk
    rcases lt_or_gt_of_ne hjk with h | h
    · exact hk.2 j h hj.1
    · exact hj.2 k h hk.1
  -- the reflection
  have hPR : ∀ _k : ℕ, MeasurePreserving (negPad (Ω₁ := Ω₁) N) P P := fun _ =>
    measurePreserving_negPad hν N
  have hEinv : ∀ k : ℕ, negPad (Ω₁ := Ω₁) N ⁻¹' E k = E k := by
    intro k
    ext ω
    simp only [Set.mem_preimage, hE, Set.mem_ofPred_eq, negPad_fst]
  have hFGk : ∀ k : ℕ, negPad (Ω₁ := Ω₁) N ⁻¹' F k = G k := by
    intro k
    ext ω
    simp only [Set.mem_preimage, hF, hG, Set.mem_ofPred_eq, padSum_negPad c k ω]
    constructor <;> intro h <;> linarith
  have hcover : ∀ k : ℕ, E k ⊆ F k ∪ G k := by
    intro k ω _
    rcases le_total (padSum c k ω) 0 with h | h
    · exact Or.inl h
    · exact Or.inr h
  -- at the first passage time the padded process is already below `−M₀`
  have hsub : ∀ k : ℕ, k ≤ N → E k ∩ F k ⊆ levSet M M₀ c N := by
    rintro k hk ω ⟨⟨h1, -⟩, h2⟩
    simp only [hF, Set.mem_ofPred_eq] at h2
    exact ⟨k, hk, by simp only [paddedProc]; linarith⟩
  have hkey := measure_le_two_mul_of_reflection_family (P := P) (N := N)
    (E := E) (F := F) (G := G) (target := levSet M M₀ c N) (R := fun _ => negPad N)
    hEm hFm hdisj hPR hEinv hFGk hcover hsub
  have hunion : (⋃ k ∈ Finset.range (N + 1), E k) = hitSet M N :=
    biUnion_firstIdx (fun (k : ℕ) (ω : Ω₁ × (Fin N → ℝ)) => M k ω.1 ≤ 0) N
  rwa [hunion] at hkey

end Padding

/-! ## 4. `hlevy` reduces to one law identification -/

section Levy

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **`hlevy` from the law of the increment vector.**

If the increment vector `inc : Ω → (Fin N → ℝ)` pushes `P` forward to a product of copies of a
symmetric law `ν`, then Lévy's maximal inequality transfers.  This reduces report 2's ≈ 700-line
`hlevy` to a **single law identification** — that the padded increments are i.i.d. — which is the
chain brief's C2 (conditional rotational invariance) applied `N` times.  No maximal inequality, no
stopping time and no conditional expectation is left for the caller. -/
theorem hlevy_of_law {P : Measure Ω} {N : ℕ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : MeasurePreserving (fun x : ℝ => -x) ν ν)
    {inc : Ω → (Fin N → ℝ)} (hinc : Measurable inc)
    (hlaw : P.map inc = Measure.pi fun _ : Fin N => ν) (r : ℝ) :
    P {ω | ∃ k ≤ N, r ≤ walkSum k (inc ω)} ≤ 2 * P {ω | r ≤ walkSum N (inc ω)} := by
  have hA : MeasurableSet {v : Fin N → ℝ | ∃ k ≤ N, r ≤ walkSum k v} := by
    have : {v : Fin N → ℝ | ∃ k ≤ N, r ≤ walkSum k v}
        = ⋃ k ∈ Finset.range (N + 1), {v : Fin N → ℝ | r ≤ walkSum k v} := by
      ext v
      simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_ofPred_eq, exists_prop]
      constructor
      · rintro ⟨k, hk, hk1⟩; exact ⟨k, Nat.lt_succ_iff.mpr hk, hk1⟩
      · rintro ⟨k, hk, hk1⟩; exact ⟨k, Nat.lt_succ_iff.mp hk, hk1⟩
    rw [this]
    exact MeasurableSet.biUnion (Finset.range (N + 1)).countable_toSet
      (fun k _ => measurableSet_le measurable_const measurable_walkSum)
  have hB : MeasurableSet {v : Fin N → ℝ | r ≤ walkSum N v} :=
    measurableSet_le measurable_const measurable_walkSum
  have e1 : P {ω | ∃ k ≤ N, r ≤ walkSum k (inc ω)}
      = (Measure.pi fun _ : Fin N => ν) {v | ∃ k ≤ N, r ≤ walkSum k v} := by
    rw [← hlaw, Measure.map_apply hinc hA]
    rfl
  have e2 : P {ω | r ≤ walkSum N (inc ω)}
      = (Measure.pi fun _ : Fin N => ν) {v | r ≤ walkSum N v} := by
    rw [← hlaw, Measure.map_apply hinc hB]
    rfl
  rw [e1, e2]
  exact levy_maximal hν N r

end Levy

/-! ## 5. The assembled tail -/

section Assembled

open ProbabilityTheory

variable {Ω₁ : Type*} [MeasurableSpace Ω₁] {N : ℕ}

/-- **Prop 4.1 in discrete form, assembled.**  `hsym` and `hlevy` — the two named inputs of
`PaddedTail.padded_increment_tail` — are now discharged from:

* `hν`  : the padding law is symmetric;
* `hincw`: `inc` is the (negated) increment vector of the padded process;
* `hincl`: the padded increments are i.i.d. `ν` — **one law identification**, owned by the chain
  brief (hinge 1's C2, conditional rotational invariance, applied `N` times);
* `hlaw` : the terminal value is `N(0, T·q²)`.

Everything else in the reflection argument is proved. -/
theorem padded_tail_assembled {P₁ : Measure Ω₁} [IsProbabilityMeasure P₁]
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : MeasurePreserving (fun x : ℝ => -x) ν ν)
    {M c : ℕ → Ω₁ → ℝ} (hM : ∀ k, Measurable (M k)) (hc : ∀ i, Measurable (c i))
    {M₀ T q : ℝ} {v : ℝ≥0}
    (hT : 0 < T) (hq : 0 < q) (hM₀ : 0 < M₀) (hv : (v : ℝ) = T * q ^ 2)
    {inc : (Ω₁ × (Fin N → ℝ)) → (Fin N → ℝ)} (hincm : Measurable inc)
    (hincw : ∀ (k : ℕ), k ≤ N → ∀ ω : Ω₁ × (Fin N → ℝ),
      walkSum k (inc ω) = -(paddedProc M M₀ c k ω))
    (hincl : (P₁.prod (Measure.pi fun _ : Fin N => ν)).map inc
      = Measure.pi fun _ : Fin N => ν)
    (hlaw : (P₁.prod (Measure.pi fun _ : Fin N => ν)).map (fun ω => walkSum N (inc ω))
      = gaussianReal 0 v) :
    (P₁.prod (Measure.pi fun _ : Fin N => ν)) (hitSet M N)
      ≤ ENNReal.ofReal (4 * Phi (M₀ / (Real.sqrt T * q))) := by
  set P : Measure (Ω₁ × (Fin N → ℝ)) := P₁.prod (Measure.pi fun _ : Fin N => ν) with hP
  have hlevset : levSet M M₀ c N = {ω | ∃ k ≤ N, M₀ ≤ walkSum k (inc ω)} := by
    ext ω
    simp only [levSet, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨k, hk, hk2⟩
      exact ⟨k, hk, by rw [hincw k hk ω]; linarith⟩
    · rintro ⟨k, hk, hk2⟩
      refine ⟨k, hk, ?_⟩
      rw [hincw k hk ω] at hk2
      linarith
  have hlevy : P (levSet M M₀ c N)
      ≤ 2 * P ((fun ω => walkSum N (inc ω)) ⁻¹' Set.Ici M₀) := by
    rw [hlevset]
    exact hlevy_of_law hν hincm hincl M₀
  exact padded_increment_tail hT hq hM₀ hv (measurable_walkSum.comp hincm)
    (hsym_of_symmetric hν hM hc M₀ N) hlevy hlaw

end Assembled

/-! ## 6. The overshoot bound

Report 2 §5.4 flagged that hinge 1's "each overshoot is one Gaussian step, `O(√h)`" is a
high-probability statement, not a deterministic one, and that a maximum over `N = 16 n³ log n`
steps carries a `√(log N)`.  Here is the union bound that supplies it: the largest of `N`
increments exceeds `a` with probability at most `2N·P(ξ ≥ a)`, so with
`a = √(2h·log(2N/ε))` the probability is at most `ε`, and `a = O(√(h log N))`. -/

section Overshoot

variable {N : ℕ}

/-- A symmetric law puts equal mass on `Ici a` and `Iic (-a)`. -/
theorem measure_Iic_neg_eq {ν : Measure ℝ} (hν : MeasurePreserving (fun x : ℝ => -x) ν ν)
    (a : ℝ) : ν (Set.Iic (-a)) = ν (Set.Ici a) := by
  have hpre : (fun x : ℝ => -x) ⁻¹' Set.Iic (-a) = Set.Ici a := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_Ici, neg_le_neg_iff]
  calc ν (Set.Iic (-a)) = (ν.map (fun x : ℝ => -x)) (Set.Iic (-a)) := by rw [hν.map_eq]
    _ = ν ((fun x : ℝ => -x) ⁻¹' Set.Iic (-a)) :=
        Measure.map_apply (by fun_prop) measurableSet_Iic
    _ = ν (Set.Ici a) := by rw [hpre]

/-- Two-sided tail of a symmetric law. -/
theorem measure_abs_ge_le {ν : Measure ℝ} (hν : MeasurePreserving (fun x : ℝ => -x) ν ν)
    (a : ℝ) : ν {x : ℝ | a ≤ |x|} ≤ 2 * ν (Set.Ici a) := by
  have hset : {x : ℝ | a ≤ |x|} = Set.Ici a ∪ Set.Iic (-a) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Ici, Set.mem_Iic, le_abs, le_neg]
  rw [hset]
  calc ν (Set.Ici a ∪ Set.Iic (-a)) ≤ ν (Set.Ici a) + ν (Set.Iic (-a)) := measure_union_le _ _
    _ = 2 * ν (Set.Ici a) := by rw [measure_Iic_neg_eq hν, two_mul]

/-- **The overshoot bound.**  For `N` i.i.d. increments with symmetric law `ν`, the largest
increment in absolute value exceeds `a` with probability at most `2N · ν(Ici a)`.

Combined with `PaddedTail.gaussianReal_Ici_le_tail`, `ν = N(0,h)` and `a = √(2h·log(2N/ε))` give
probability `≤ ε`; so with `N = 16 n³ log n` steps every increment is `O(√(h log n))`, which is the
`√(log N)` factor report 2 §5.4 flagged as missing from hinge 1's `O(√h)`.  The projection-overshoot
error is therefore `n² · O(√(h log n)) = O(n^{-1/2} √(log n)) = o(1)` at `h = n⁻⁵`, and the `n²`
still survives. -/
theorem max_coord_tail {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : MeasurePreserving (fun x : ℝ => -x) ν ν) (N : ℕ) (a : ℝ) :
    (Measure.pi fun _ : Fin N => ν) {ω : Fin N → ℝ | ∃ i : Fin N, a ≤ |ω i|}
      ≤ 2 * N * ν (Set.Ici a) := by
  have hmarg : ∀ i : Fin N, (Measure.pi fun _ : Fin N => ν) {ω : Fin N → ℝ | a ≤ |ω i|}
      = ν {x : ℝ | a ≤ |x|} := by
    intro i
    classical
    have hmp := MeasureTheory.measurePreserving_eval (μ := fun _ : Fin N => ν) i
    have hms : MeasurableSet {x : ℝ | a ≤ |x|} :=
      measurableSet_le measurable_const measurable_norm
    calc (Measure.pi fun _ : Fin N => ν) {ω : Fin N → ℝ | a ≤ |ω i|}
        = (Measure.pi fun _ : Fin N => ν) ((fun ω : Fin N → ℝ => ω i) ⁻¹' {x : ℝ | a ≤ |x|}) := rfl
      _ = ((Measure.pi fun _ : Fin N => ν).map (fun ω : Fin N → ℝ => ω i)) {x : ℝ | a ≤ |x|} :=
          (Measure.map_apply (measurable_pi_apply i) hms).symm
      _ = ν {x : ℝ | a ≤ |x|} := by rw [hmp.map_eq]
  have hunion : {ω : Fin N → ℝ | ∃ i : Fin N, a ≤ |ω i|}
      = ⋃ i : Fin N, {ω : Fin N → ℝ | a ≤ |ω i|} := by
    ext ω; simp
  rw [hunion]
  calc (Measure.pi fun _ : Fin N => ν) (⋃ i : Fin N, {ω : Fin N → ℝ | a ≤ |ω i|})
      ≤ ∑ i : Fin N, (Measure.pi fun _ : Fin N => ν) {ω : Fin N → ℝ | a ≤ |ω i|} :=
        measure_iUnion_fintype_le _ _
    _ = ∑ _i : Fin N, ν {x : ℝ | a ≤ |x|} := Finset.sum_congr rfl (fun i _ => hmarg i)
    _ = N * ν {x : ℝ | a ≤ |x|} := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ N * (2 * ν (Set.Ici a)) := by gcongr; exact measure_abs_ge_le hν a
    _ = 2 * N * ν (Set.Ici a) := by ring

end Overshoot

/-! ## 7. The terminal law

The last premise of `padded_tail_assembled`, `hlaw`, is derivable from `hincl`: if the padded
increments are i.i.d. `N(0,δ)` then their sum is `N(0, N·δ)`.  With that, the chain brief owes
**one** fact and no more — the law of the increment vector. -/

section TerminalLaw

open ProbabilityTheory

/-- The sum over a `Finset` of i.i.d. centred Gaussian coordinates is centred Gaussian. -/
theorem map_finsetSum_gaussian {N : ℕ} {δ : ℝ≥0} (s : Finset (Fin N)) :
    (Measure.pi fun _ : Fin N => gaussianReal 0 δ).map (fun v : Fin N → ℝ => ∑ i ∈ s, v i)
      = gaussianReal 0 (s.card • δ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty, Finset.card_empty, zero_smul, gaussianReal_zero_var]
      rw [Measure.map_const]
      simp
  | insert a s ha ih =>
      have hindep : iIndepFun (fun (i : Fin N) (v : Fin N → ℝ) => v i)
          (Measure.pi fun _ : Fin N => gaussianReal 0 δ) :=
        iIndepFun_pi (X := fun _ : Fin N => (id : ℝ → ℝ)) (fun _ => aemeasurable_id)
      have hXY : IndepFun (fun v : Fin N → ℝ => v a) (fun v : Fin N → ℝ => ∑ i ∈ s, v i)
          (Measure.pi fun _ : Fin N => gaussianReal 0 δ) := by
        have h0 := hindep.indepFun_finsetSum_of_notMem (fun i => measurable_pi_apply i) ha
        have hfe : (∑ j ∈ s, fun v : Fin N → ℝ => v j)
            = (fun v : Fin N → ℝ => ∑ i ∈ s, v i) := by
          funext v; simp
        rw [hfe] at h0
        exact h0.symm
      have hX : HasLaw (fun v : Fin N → ℝ => v a) (gaussianReal 0 δ)
          (Measure.pi fun _ : Fin N => gaussianReal 0 δ) :=
        (MeasureTheory.measurePreserving_eval (μ := fun _ : Fin N => gaussianReal 0 δ) a).hasLaw
      have hY : HasLaw (fun v : Fin N → ℝ => ∑ i ∈ s, v i)
          (gaussianReal 0 (s.card • δ)) (Measure.pi fun _ : Fin N => gaussianReal 0 δ) :=
        ⟨(by fun_prop), ih⟩
      have hsum := gaussianReal_add_gaussianReal_of_indepFun hXY hX hY
      have hfun : (fun v : Fin N → ℝ => ∑ i ∈ insert a s, v i)
          = (fun v : Fin N → ℝ => v a) + (fun v : Fin N → ℝ => ∑ i ∈ s, v i) := by
        funext v
        simp [Finset.sum_insert ha]
      rw [hfun, hsum, Finset.card_insert_of_notMem ha]
      have hvar : (s.card + 1) • δ = δ + s.card • δ := by
        rw [add_smul, one_smul]
        exact add_comm _ _
      rw [hvar]
      norm_num

/-- **The terminal law.**  The walk's final value under i.i.d. `N(0,δ)` increments is `N(0, N·δ)`. -/
theorem map_walkSum_gaussian {N : ℕ} {δ : ℝ≥0} :
    (Measure.pi fun _ : Fin N => gaussianReal 0 δ).map (walkSum N)
      = gaussianReal 0 ((N : ℕ) • δ) := by
  have hfun : walkSum (N := N) N = fun v : Fin N → ℝ => ∑ i ∈ Finset.univ, v i := by
    funext v
    exact walkSum_total v
  rw [hfun, map_finsetSum_gaussian Finset.univ, Finset.card_univ, Fintype.card_fin]

/-- **`hlaw` from `hincl`.**  If the increment vector is i.i.d. `N(0,δ)`, the terminal value is
`N(0, N·δ)` — so `padded_tail_assembled`'s last premise is free. -/
theorem hlaw_of_hincl {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {N : ℕ} {δ : ℝ≥0}
    {inc : Ω → (Fin N → ℝ)} (hincm : Measurable inc)
    (hincl : P.map inc = Measure.pi fun _ : Fin N => gaussianReal 0 δ) :
    P.map (fun ω => walkSum N (inc ω)) = gaussianReal 0 ((N : ℕ) • δ) := by
  have hcomp : (fun ω => walkSum N (inc ω)) = (walkSum (N := N) N) ∘ inc := rfl
  rw [hcomp, ← Measure.map_map measurable_walkSum hincm, hincl, map_walkSum_gaussian]

/-- A centred real Gaussian is symmetric. -/
theorem measurePreserving_neg_gaussianReal (δ : ℝ≥0) :
    MeasurePreserving (fun x : ℝ => -x) (gaussianReal 0 δ) (gaussianReal 0 δ) :=
  ⟨by fun_prop, by simpa using gaussianReal_map_neg (μ := (0 : ℝ)) (v := δ)⟩

/-- **Prop 4.1 in discrete form, from a single hypothesis.**

Only `hincl` is left: the padded increment vector is i.i.d. `N(0,δ)`.  Symmetry of the padding,
the reflection at the first passage time, Lévy's maximal inequality, the terminal law and the
Gaussian tail with its `1/r` are all proved.  The constant is `4 = 2 · 2`, against the paper's 2:
one factor from conditional symmetry, one from Lévy; report 2 §5.2 (L5) prices that as a change to
the universal constant `c` only, not to the `n²`. -/
theorem padded_tail_of_increments {Ω₁ : Type*} [MeasurableSpace Ω₁] {P₁ : Measure Ω₁}
    [IsProbabilityMeasure P₁] {N : ℕ} {δ : ℝ≥0}
    {M c : ℕ → Ω₁ → ℝ} (hM : ∀ k, Measurable (M k)) (hc : ∀ i, Measurable (c i))
    {M₀ T q : ℝ} (hT : 0 < T) (hq : 0 < q) (hM₀ : 0 < M₀)
    (hv : (((N : ℕ) • δ : ℝ≥0) : ℝ) = T * q ^ 2)
    {inc : (Ω₁ × (Fin N → ℝ)) → (Fin N → ℝ)} (hincm : Measurable inc)
    (hincw : ∀ (k : ℕ), k ≤ N → ∀ ω : Ω₁ × (Fin N → ℝ),
      walkSum k (inc ω) = -(paddedProc M M₀ c k ω))
    (hincl : (P₁.prod (Measure.pi fun _ : Fin N => gaussianReal 0 δ)).map inc
      = Measure.pi fun _ : Fin N => gaussianReal 0 δ) :
    (P₁.prod (Measure.pi fun _ : Fin N => gaussianReal 0 δ)) (hitSet M N)
      ≤ ENNReal.ofReal (4 * Phi (M₀ / (Real.sqrt T * q))) :=
  padded_tail_assembled (measurePreserving_neg_gaussianReal δ) hM hc hT hq hM₀ hv
    hincm hincw hincl (hlaw_of_hincl hincm hincl)

end TerminalLaw

end Submission.L10

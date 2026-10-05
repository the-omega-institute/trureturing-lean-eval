import Mathlib

/-!
# Gate L-10 (`klartag_packing`) — Construction A with `k = 1`, replacing Siegel's formula

Brief 3, goal 2–3.  Klartag's §5 (arXiv:2504.05042, p. 22, eqs. 63–66) uses the Siegel mean
value theorem twice, both times as an **upper** bound on a first moment fed to Markov.  The
`p`-ary Construction-A ensemble supplies exactly that, and because the ensemble is finite,
§5 needs no measure theory at all: Markov becomes "if a finite average is `< 1` then some
term is `< 1`".

For a prime `p` and `g ∈ (ZMod p)ⁿ ∖ {0}`,

  `Λ(g) = {y ∈ ℤⁿ : y mod p ∈ ⟨g⟩}`,     `L(g) = α · Λ(g)`.

## Main results

Counting (the ensemble is finite — this is all of the probability there is):

* `card_filter_onLine` — a nonzero residue lies on exactly `p - 1` of the lines `⟨g⟩`.
* `sum_card_filter_onLine` — **the first-moment lemma**, the swap of two finite sums:
  `Σ_g #(A ∩ Λ(g)) = (p-1)·|A|` for any finite `A ⊆ ℤⁿ` of `p`-indivisible points.
* `sum_card_le` — the density bound `p^{n-1}·Σ_{g≠0} #(A ∩ Λ(g)) ≤ (pⁿ-1)·|A|`, i.e. the
  average over the `pⁿ-1` nonzero `g` is at most `|A|·p^{1-n}`, division-free.
* `redMod_ne_zero_of_abs_lt` — error term 1: the `pℤⁿ` sum vanishes identically once `p`
  exceeds the radius of the support (`p ≳ (0.27√n)ⁿ`; `p` appears nowhere in the conclusion).
* `card_bad_one_le`, `card_bad_two_le` — the discrete counterparts of eqs. (64) and (66).
* `exists_line_avoiding` — **Proposition 5.1's finite skeleton**: the union bound with its
  slack, delivering a nonzero `g` whose line misses `A` and carries `< θ` points of `B`.

The lattice (this is where Mathlib is thin):

* `discreteTopology_of_le`, `span_real_eq_top_of_smul_le` — the generic criterion
  *a subgroup of a `ℤ`-lattice that contains `k·L` is a `ℤ`-lattice*, which hinge 2 listed as
  absent from Mathlib.  Stated for an arbitrary real normed space, not for `Fin n → ℝ`.
* `instDiscreteLatR`, `instZLatticeLatR` — `Λ(g) ⊆ ℝⁿ` is a `ℤ`-lattice.
* `index_latZ`, `relIndex_latR` — `[ℤⁿ : Λ(g)] = p^{n-1}`.
* `covolume_intLat`, `covolume_latR` — `covol Λ(g) = p^{n-1}`, via
  `ZLattice.covolume_div_covolume_eq_relIndex`.

Scaling by `α := κ_n^{1/n}·p^{(1-n)/n}` then puts `covol L(g) = κ_n` exactly, so `L(g)` lies
in Klartag's `X_n` on the nose; see `research/gate-l10/reports/3-section5.md` for the one
remaining covolume step (`covolume (r • L) = |r|^n · covolume L`) and its entry point.
-/

open Finset Submodule Module

namespace Submission.L10.ConstructionA

variable {p n : ℕ}


/-- Coordinatewise reduction `ℤⁿ → (ZMod p)ⁿ`. -/
def redMod (p : ℕ) {n : ℕ} (y : Fin n → ℤ) : Fin n → ZMod p := fun i => ((y i : ℤ) : ZMod p)

/-- Construction A with `k = 1`: the residue `v` lies on the line `C_g = ⟨g⟩`. -/
def OnLine {p n : ℕ} (g v : Fin n → ZMod p) : Prop := ∃ u : ZMod p, u • g = v

instance decidableOnLine [NeZero p] (g v : Fin n → ZMod p) : Decidable (OnLine g v) := by
  unfold OnLine; infer_instance

theorem onLine_iff_mem_span [Fact (Nat.Prime p)] (g v : Fin n → ZMod p) :
    OnLine g v ↔ v ∈ Submodule.span (ZMod p) ({g} : Set (Fin n → ZMod p)) :=
  (Submodule.mem_span_singleton).symm

theorem onLine_zero_iff [NeZero p] (v : Fin n → ZMod p) : OnLine 0 v ↔ v = 0 := by
  constructor
  · rintro ⟨u, hu⟩; rw [← hu, smul_zero]
  · rintro rfl; exact ⟨0, smul_zero 0⟩

/-- **The line count.** A nonzero residue lies on exactly `p - 1` lines `⟨g⟩`. -/
theorem card_filter_onLine [Fact (Nat.Prime p)] (v : Fin n → ZMod p) (hv : v ≠ 0) :
    (Finset.univ.filter (fun g : Fin n → ZMod p => OnLine g v)).card = p - 1 := by
  classical
  have hset : (Finset.univ.filter (fun g : Fin n → ZMod p => OnLine g v))
      = (Finset.univ.erase (0 : ZMod p)).image (fun u : ZMod p => u • v) := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_erase]
    constructor
    · rintro ⟨u, hu⟩
      have hu0 : u ≠ 0 := by rintro rfl; exact hv (by rw [← hu, zero_smul])
      exact ⟨u⁻¹, ⟨inv_ne_zero hu0, trivial⟩, by
        rw [← hu, smul_smul, inv_mul_cancel₀ hu0, one_smul]⟩
    · rintro ⟨u, ⟨hu0, -⟩, rfl⟩
      exact ⟨u⁻¹, by rw [smul_smul, inv_mul_cancel₀ hu0, one_smul]⟩
  rw [hset, Finset.card_image_of_injOn, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, ZMod.card]
  intro a _ b _ hab
  set_option backward.isDefEq.respectTransparency false in
    exact smul_left_injective (ZMod p) hv hab

/-- **First-moment lemma (exact form).**  Summing over *all* `g`, the total number of
incidences between a finite set `A` of `p`-indivisible integer points and the lines `⟨g⟩`
is exactly `(p - 1) * |A|`.  This is the swap of two finite sums. -/
theorem sum_card_filter_onLine [Fact (Nat.Prime p)] (A : Finset (Fin n → ℤ))
    (hA : ∀ y ∈ A, redMod p y ≠ 0) :
    ∑ g : Fin n → ZMod p, (A.filter (fun y => OnLine g (redMod p y))).card
      = (p - 1) * A.card := by
  classical
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun y hy => ?_)]
  · rw [Finset.sum_const, smul_eq_mul, mul_comm]
  · show ∑ g : Fin n → ZMod p, (if OnLine g (redMod p y) then 1 else 0) = p - 1
    rw [← Finset.card_filter]
    exact card_filter_onLine _ (hA y hy)

/-- The `g = 0` line carries no `p`-indivisible point, so the sum over `g ≠ 0` is the same. -/
theorem sum_card_filter_onLine_erase [Fact (Nat.Prime p)] (A : Finset (Fin n → ℤ))
    (hA : ∀ y ∈ A, redMod p y ≠ 0) :
    ∑ g ∈ Finset.univ.erase (0 : Fin n → ZMod p),
        (A.filter (fun y => OnLine g (redMod p y))).card
      = (p - 1) * A.card := by
  classical
  rw [← sum_card_filter_onLine A hA, eq_comm,
    ← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : Fin n → ZMod p))]
  have hzero : (A.filter (fun y => OnLine (0 : Fin n → ZMod p) (redMod p y))).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro y hy hcon
    exact hA y hy ((onLine_zero_iff _).1 hcon)
  rw [hzero, add_zero]

/-! ### The density bound `(p-1)/(pⁿ-1) ≤ p^{1-n}` -/

theorem succ_le_pow (hp : 1 ≤ p) (hn : 1 ≤ n) :
    (p - 1) * p ^ (n - 1) + 1 ≤ p ^ n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h1 : 1 ≤ p ^ k := Nat.one_le_pow _ _ (by omega)
  have h2 : (p - 1) * p ^ k + p ^ k = p * p ^ k := by
    cases p with
    | zero => omega
    | succ q => simp; ring
  simp only [Nat.add_sub_cancel]
  rw [pow_succ, mul_comm (p ^ k) p]
  omega

/-- **The density bound, division-free.**  `p^{n-1} · Σ_{g≠0} (count) ≤ (pⁿ - 1) · |A|`,
i.e. the average over the `pⁿ - 1` nonzero `g` is at most `|A| · p^{1-n}`. -/
theorem sum_card_le [Fact (Nat.Prime p)] (hn : 1 ≤ n) (A : Finset (Fin n → ℤ))
    (hA : ∀ y ∈ A, redMod p y ≠ 0) :
    p ^ (n - 1) * (∑ g ∈ Finset.univ.erase (0 : Fin n → ZMod p),
        (A.filter (fun y => OnLine g (redMod p y))).card)
      ≤ (p ^ n - 1) * A.card := by
  have hp : 1 ≤ p := (Fact.out (p := Nat.Prime p)).one_lt.le.trans' (by norm_num)
  rw [sum_card_filter_onLine_erase A hA]
  have key : (p - 1) * p ^ (n - 1) + 1 ≤ p ^ n := succ_le_pow hp hn
  have : p ^ (n - 1) * ((p - 1) * A.card) = ((p - 1) * p ^ (n - 1)) * A.card := by ring
  rw [this]
  exact Nat.mul_le_mul_right _ (by omega)

/-! ### Markov and the union bound -/

/-- **Finite Markov.**  The number of indices where a nonnegative `f` reaches `θ` is at most
`(Σ f)/θ`, in the division-free form `#{f ≥ θ} · θ ≤ Σ f`. -/
theorem card_filter_mul_le_sum {ι : Type*} [DecidableEq ι] {s : Finset ι} {f : ι → ℝ}
    (hf : ∀ i ∈ s, 0 ≤ f i) {θ : ℝ} :
    ((s.filter (fun i => θ ≤ f i)).card : ℝ) * θ ≤ ∑ i ∈ s, f i := by
  classical
  calc ((s.filter (fun i => θ ≤ f i)).card : ℝ) * θ
      = ∑ _i ∈ s.filter (fun i => θ ≤ f i), θ := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ s.filter (fun i => θ ≤ f i), f i :=
        Finset.sum_le_sum (fun i hi => (Finset.mem_filter.1 hi).2)
    _ ≤ ∑ i ∈ s, f i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i hi _ => hf i hi)

/-- **The union bound / selection step** (`1/2 + 1/e < 1`): if the two bad sets together
miss some element of `s`, a good `g` exists. -/
theorem exists_mem_not_mem {ι : Type*} [DecidableEq ι] {s B₁ B₂ : Finset ι}
    (h : B₁.card + B₂.card < s.card) : ∃ i ∈ s, i ∉ B₁ ∧ i ∉ B₂ := by
  classical
  have hne : (s \ (B₁ ∪ B₂)).Nonempty := by
    rw [← Finset.card_pos]
    have h1 : (B₁ ∪ B₂).card ≤ B₁.card + B₂.card := Finset.card_union_le _ _
    have h2 : s.card - (B₁ ∪ B₂).card ≤ (s \ (B₁ ∪ B₂)).card := Finset.le_card_sdiff _ _
    omega
  obtain ⟨i, hi⟩ := hne
  rw [Finset.mem_sdiff, Finset.mem_union] at hi
  exact ⟨i, hi.1, fun hc => hi.2 (Or.inl hc), fun hc => hi.2 (Or.inr hc)⟩

/-! ### The `p`-divisible points are far away -/

/-- A nonzero integer point all of whose coordinates are divisible by `p` has a coordinate of
absolute value at least `p`.  This is why the `pℤⁿ` term of the first-moment lemma vanishes
identically once `p` exceeds the radius of the support. -/
theorem le_abs_of_dvd {y : Fin n → ℤ} (hdvd : ∀ i, (p : ℤ) ∣ y i) {j : Fin n} (hj : y j ≠ 0) :
    (p : ℤ) ≤ |y j| :=
  Int.le_of_dvd (abs_pos.2 hj) ((dvd_abs _ _).2 (hdvd j))


/-! ### `p`-divisible points vanish for large `p` -/

/-- **Error term 1.**  If every point of `A` has all coordinates of absolute value `< p`,
then no nonzero point of `A` is divisible by `p`: the `pℤⁿ` term of the first-moment lemma
is identically zero.  Klartag's `φ`s are supported in `|x| ≤ 1.1`, so with `α ≈ √(2πe/n)/p`
this holds as soon as `p > (1.1/κ_n^{1/n})ⁿ ≍ (0.27√n)ⁿ`. -/
theorem redMod_ne_zero_of_abs_lt [NeZero p] {A : Finset (Fin n → ℤ)}
    (h0 : (0 : Fin n → ℤ) ∉ A) (hbd : ∀ y ∈ A, ∀ i, |y i| < (p : ℤ)) :
    ∀ y ∈ A, redMod p y ≠ 0 := by
  intro y hy hzero
  have hdvd : ∀ i, (p : ℤ) ∣ y i := by
    intro i
    have : ((y i : ℤ) : ZMod p) = 0 := congrFun hzero i
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 this
  have hy0 : y = 0 := by
    funext i
    by_contra hne
    exact absurd (le_abs_of_dvd hdvd hne) (not_le.2 (hbd y hy i))
  exact h0 (hy0 ▸ hy)

/-! ### Markov in `ℕ` and the selection step (Proposition 5.1's finite skeleton) -/

/-- **Markov, `ℕ` form.** -/
theorem card_filter_mul_le_sum_nat {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℕ)
    (θ : ℕ) : (s.filter (fun i => θ ≤ f i)).card * θ ≤ ∑ i ∈ s, f i := by
  classical
  calc (s.filter (fun i => θ ≤ f i)).card * θ = ∑ _i ∈ s.filter (fun i => θ ≤ f i), θ := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ i ∈ s.filter (fun i => θ ≤ f i), f i :=
        Finset.sum_le_sum (fun i hi => (Finset.mem_filter.1 hi).2)
    _ ≤ ∑ i ∈ s, f i := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- The number of nonzero `g` is `pⁿ - 1`. -/
theorem card_erase_univ [NeZero p] :
    (Finset.univ.erase (0 : Fin n → ZMod p)).card = p ^ n - 1 := by
  classical
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  simp [ZMod.card]

/-- **Use 1's Markov step (eq. 64), discrete counterpart.**  The number of lines meeting the
finite set `A` at all is at most `(pⁿ-1)·|A|/p^{n-1}`. -/
theorem card_bad_one_le [Fact (Nat.Prime p)] (hn : 1 ≤ n) (A : Finset (Fin n → ℤ))
    (hA : ∀ y ∈ A, redMod p y ≠ 0) :
    p ^ (n - 1) *
        ((Finset.univ.erase (0 : Fin n → ZMod p)).filter
          (fun g => ∃ y ∈ A, OnLine g (redMod p y))).card
      ≤ (p ^ n - 1) * A.card := by
  classical
  refine le_trans (Nat.mul_le_mul_left _ ?_) (sum_card_le hn A hA)
  calc ((Finset.univ.erase (0 : Fin n → ZMod p)).filter
          (fun g => ∃ y ∈ A, OnLine g (redMod p y))).card
      = ∑ _g ∈ (Finset.univ.erase (0 : Fin n → ZMod p)).filter
          (fun g => ∃ y ∈ A, OnLine g (redMod p y)), 1 := by
        rw [Finset.sum_const, smul_eq_mul, mul_one]
    _ ≤ ∑ g ∈ (Finset.univ.erase (0 : Fin n → ZMod p)).filter
          (fun g => ∃ y ∈ A, OnLine g (redMod p y)),
          (A.filter (fun y => OnLine g (redMod p y))).card := by
        refine Finset.sum_le_sum (fun g hg => ?_)
        obtain ⟨y, hy, hyg⟩ := (Finset.mem_filter.1 hg).2
        exact Finset.card_pos.2 ⟨y, Finset.mem_filter.2 ⟨hy, hyg⟩⟩
    _ ≤ ∑ g ∈ Finset.univ.erase (0 : Fin n → ZMod p),
          (A.filter (fun y => OnLine g (redMod p y))).card :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- **Use 2's Markov step (eq. 66), discrete counterpart.** -/
theorem card_bad_two_le [Fact (Nat.Prime p)] (hn : 1 ≤ n) (B : Finset (Fin n → ℤ))
    (hB : ∀ y ∈ B, redMod p y ≠ 0) (θ : ℕ) :
    θ * (p ^ (n - 1) *
        ((Finset.univ.erase (0 : Fin n → ZMod p)).filter
          (fun g => θ ≤ (B.filter (fun y => OnLine g (redMod p y))).card)).card)
      ≤ (p ^ n - 1) * B.card := by
  classical
  refine le_trans ?_ (sum_card_le hn B hB)
  rw [← mul_assoc, mul_comm θ (p ^ (n - 1)), mul_assoc]
  exact Nat.mul_le_mul_left _ (by
    rw [mul_comm]
    exact card_filter_mul_le_sum_nat _ _ θ)

/-- **Proposition 5.1's finite skeleton.**  With `|A| + |B|/θ < p^{n-1}` there is a nonzero `g`
whose line misses `A` altogether and carries fewer than `θ` points of `B`.  The union bound's
slack (`1 - 1/2 - 1/e = 0.1321` in the paper) is exactly the strictness of `hroom`. -/
theorem exists_line_avoiding [Fact (Nat.Prime p)] (hn : 1 ≤ n)
    (A B : Finset (Fin n → ℤ)) (hA : ∀ y ∈ A, redMod p y ≠ 0) (hB : ∀ y ∈ B, redMod p y ≠ 0)
    (θ : ℕ) (_hθ : 0 < θ) (hroom : θ * A.card + B.card < θ * p ^ (n - 1)) :
    ∃ g : Fin n → ZMod p, g ≠ 0 ∧ (∀ y ∈ A, ¬ OnLine g (redMod p y)) ∧
      (B.filter (fun y => OnLine g (redMod p y))).card < θ := by
  classical
  set s : Finset (Fin n → ZMod p) := Finset.univ.erase 0 with hs
  set B₁ := s.filter (fun g => ∃ y ∈ A, OnLine g (redMod p y)) with hB₁
  set B₂ := s.filter (fun g => θ ≤ (B.filter (fun y => OnLine g (redMod p y))).card) with hB₂
  have hppos : 0 < p ^ (n - 1) := pow_pos (Fact.out (p := Nat.Prime p)).pos _
  have h1 : p ^ (n - 1) * B₁.card ≤ (p ^ n - 1) * A.card := card_bad_one_le hn A hA
  have h2 : θ * (p ^ (n - 1) * B₂.card) ≤ (p ^ n - 1) * B.card := card_bad_two_le hn B hB θ
  have hcard : s.card = p ^ n - 1 := card_erase_univ
  have hlt : B₁.card + B₂.card < s.card := by
    rw [hcard]
    by_contra hcon
    push Not at hcon
    have hkey : θ * p ^ (n - 1) * (p ^ n - 1)
        ≤ (p ^ n - 1) * (θ * A.card + B.card) := by
      calc θ * p ^ (n - 1) * (p ^ n - 1)
          ≤ θ * p ^ (n - 1) * (B₁.card + B₂.card) := Nat.mul_le_mul_left _ hcon
        _ = θ * (p ^ (n - 1) * B₁.card) + θ * (p ^ (n - 1) * B₂.card) := by ring
        _ ≤ θ * ((p ^ n - 1) * A.card) + (p ^ n - 1) * B.card :=
            Nat.add_le_add (Nat.mul_le_mul_left _ h1) h2
        _ = (p ^ n - 1) * (θ * A.card + B.card) := by ring
    have hpn : 0 < p ^ n - 1 := by
      have : 1 < p ^ n := by
        calc 1 < p := (Fact.out (p := Nat.Prime p)).one_lt
          _ = p ^ 1 := (pow_one p).symm
          _ ≤ p ^ n := Nat.pow_le_pow_right (Fact.out (p := Nat.Prime p)).pos hn
      omega
    have hkey' : (p ^ n - 1) * (θ * p ^ (n - 1)) ≤ (p ^ n - 1) * (θ * A.card + B.card) := by
      calc (p ^ n - 1) * (θ * p ^ (n - 1)) = θ * p ^ (n - 1) * (p ^ n - 1) := by ring
        _ ≤ (p ^ n - 1) * (θ * A.card + B.card) := hkey
    have hfin := Nat.le_of_mul_le_mul_left hkey' hpn
    omega
  obtain ⟨g, hgs, hg1, hg2⟩ := exists_mem_not_mem hlt
  refine ⟨g, (Finset.mem_erase.1 hgs).1, ?_, ?_⟩
  · intro y hy hcon
    exact hg1 (Finset.mem_filter.2 ⟨hgs, ⟨y, hy, hcon⟩⟩)
  · by_contra hcon
    exact hg2 (Finset.mem_filter.2 ⟨hgs, not_lt.1 hcon⟩)


/-! ### A sublattice of a `ℤ`-lattice that contains `k · L` is a `ℤ`-lattice -/

/-- **Generic sublattice criterion** (absent from Mathlib).  If `M ≤ L` with `L` a `ℤ`-lattice
and `M ⊇ k · L` for some `k ≠ 0`, then `M` is a `ℤ`-lattice. -/
theorem discreteTopology_of_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L M : Submodule ℤ E) [DiscreteTopology L] (hML : M ≤ L) :
    DiscreteTopology M :=
  DiscreteTopology.of_subset (s := (L : Set E)) inferInstance hML

theorem span_real_eq_top_of_smul_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L M : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {k : ℕ} (hk : k ≠ 0) (hkL : ∀ x ∈ L, (k : ℤ) • x ∈ M) :
    Submodule.span ℝ (M : Set E) = ⊤ := by
  have hL : Submodule.span ℝ (L : Set E) = ⊤ := IsZLattice.span_top
  rw [eq_top_iff, ← hL, Submodule.span_le]
  intro x hx
  have h1 : ((k : ℤ) • x) ∈ M := hkL x hx
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk
  have h2 : ((k : ℤ) • x : E) = (k : ℝ) • x := by
    rw [← Int.cast_smul_eq_zsmul ℝ]; norm_num
  have h3 : x = (k : ℝ)⁻¹ • ((k : ℝ) • x) := (inv_smul_smul₀ hk0 x).symm
  rw [SetLike.mem_coe, h3, ← h2]
  exact Submodule.smul_mem _ _ (Submodule.subset_span h1)

/-! ### The maps `ℤⁿ → ℝⁿ` and `ℤⁿ → (ZMod p)ⁿ` -/

/-- The `ℤ`-linear inclusion `ℤⁿ ↪ ℝⁿ`. -/
def toReal (n : ℕ) : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℝ) where
  toFun y := fun i => (y i : ℝ)
  map_add' y z := by funext i; simp
  map_smul' m y := by funext i; simp [zsmul_eq_mul]

theorem toReal_apply (y : Fin n → ℤ) (i : Fin n) : toReal n y i = (y i : ℝ) := rfl

theorem toReal_injective : Function.Injective (toReal n) := by
  intro y z h
  funext i
  have hi := congrFun h i
  rw [toReal_apply, toReal_apply] at hi
  exact_mod_cast hi

/-- Coordinatewise reduction `ℤⁿ → (ZMod p)ⁿ`, as a `ℤ`-linear map. -/
def redLin (p n : ℕ) : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ZMod p) where
  toFun y := fun i => ((y i : ℤ) : ZMod p)
  map_add' y z := by funext i; simp
  map_smul' m y := by funext i; simp [zsmul_eq_mul]

theorem redLin_apply (y : Fin n → ℤ) (i : Fin n) : redLin p n y i = ((y i : ℤ) : ZMod p) := rfl

theorem redLin_surjective [NeZero p] : Function.Surjective (redLin p n) := by
  intro v
  refine ⟨fun i => (ZMod.cast (v i) : ℤ), ?_⟩
  funext i
  simp [redLin_apply]

/-! ### Construction A -/

/-- The `p`-ary line `C_g = ⟨g⟩`, as a `ℤ`-submodule. -/
def lineZ (g : Fin n → ZMod p) : Submodule ℤ (Fin n → ZMod p) :=
  (Submodule.span (ZMod p) ({g} : Set (Fin n → ZMod p))).restrictScalars ℤ

/-- **Construction A in `ℤⁿ`**: `Λ₀(g) = {y ∈ ℤⁿ : y mod p ∈ ⟨g⟩}`. -/
def latZ (p n : ℕ) (g : Fin n → ZMod p) : Submodule ℤ (Fin n → ℤ) :=
  Submodule.comap (redLin p n) (lineZ g)

theorem mem_latZ (g : Fin n → ZMod p) (y : Fin n → ℤ) :
    y ∈ latZ p n g ↔ ∃ u : ZMod p, u • g = redLin p n y := by
  simp only [latZ, Submodule.mem_comap, lineZ, Submodule.restrictScalars_mem,
    Submodule.mem_span_singleton]

/-- `Λ₀(g)` contains `p·ℤⁿ`. -/
theorem smul_mem_latZ (g : Fin n → ZMod p) (y : Fin n → ℤ) : (p : ℤ) • y ∈ latZ p n g := by
  rw [mem_latZ]
  refine ⟨0, ?_⟩
  rw [zero_smul]
  funext i
  simp [redLin_apply]

/-- The standard integer lattice in `ℝⁿ`. -/
def intLat (n : ℕ) : Submodule ℤ (Fin n → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))

theorem intLat_eq_range (n : ℕ) : intLat n = LinearMap.range (toReal n) := by
  apply le_antisymm
  · rw [intLat, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨fun j => if j = i then 1 else 0, by
      funext j; simp [toReal_apply, Pi.basisFun_apply, Pi.single_apply, eq_comm]⟩
  · rintro _ ⟨y, rfl⟩
    have : toReal n y = ∑ i : Fin n, y i • (Pi.basisFun ℝ (Fin n)) i := by
      funext j
      simp [toReal_apply, Pi.basisFun_apply, Pi.single_apply, zsmul_eq_mul]
    rw [this]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨i, rfl⟩))

instance instDiscreteIntLat (n : ℕ) : DiscreteTopology (intLat n) :=
  inferInstanceAs (DiscreteTopology (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))))

instance instZLatticeIntLat (n : ℕ) : IsZLattice ℝ (intLat n) :=
  inferInstanceAs (IsZLattice ℝ (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))))

/-- **Construction A in `ℝⁿ`**: `Λ(g) = {x ∈ ℤⁿ : x mod p ∈ ⟨g⟩} ⊆ ℝⁿ`. -/
def latR (p n : ℕ) (g : Fin n → ZMod p) : Submodule ℤ (Fin n → ℝ) :=
  Submodule.map (toReal n) (latZ p n g)

theorem latR_le_intLat (g : Fin n → ZMod p) : latR p n g ≤ intLat n := by
  rw [intLat_eq_range]
  rintro _ ⟨y, -, rfl⟩
  exact ⟨y, rfl⟩

theorem smul_intLat_le_latR (g : Fin n → ZMod p) :
    ∀ x ∈ intLat n, (p : ℤ) • x ∈ latR p n g := by
  rw [intLat_eq_range]
  rintro _ ⟨y, rfl⟩
  exact ⟨(p : ℤ) • y, smul_mem_latZ g y, by rw [map_smul]⟩

instance instDiscreteLatR (g : Fin n → ZMod p) : DiscreteTopology (latR p n g) :=
  discreteTopology_of_le (intLat n) _ (latR_le_intLat g)

instance instZLatticeLatR [NeZero p] (g : Fin n → ZMod p) : IsZLattice ℝ (latR p n g) where
  span_top := span_real_eq_top_of_smul_le (intLat n) (latR p n g)
    (NeZero.ne p) (smul_intLat_le_latR g)



/-! ### The index of Construction A -/

theorem natCard_lineZ [Fact (Nat.Prime p)] (g : Fin n → ZMod p) (hg : g ≠ 0) :
    Nat.card (Submodule.span (ZMod p) ({g} : Set (Fin n → ZMod p))) = p := by
  set_option backward.isDefEq.respectTransparency false in
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), finrank_span_singleton hg,
      pow_one, Nat.card_zmod]

theorem natCard_lineZ' [Fact (Nat.Prime p)] (g : Fin n → ZMod p) (hg : g ≠ 0) :
    Nat.card (lineZ g).toAddSubgroup = p := natCard_lineZ g hg

theorem index_lineZ [Fact (Nat.Prime p)] (hn : 1 ≤ n) (g : Fin n → ZMod p) (hg : g ≠ 0) :
    (lineZ g).toAddSubgroup.index = p ^ (n - 1) := by
  have : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).ne_zero⟩
  have hmul := AddSubgroup.card_mul_index (lineZ g).toAddSubgroup
  rw [natCard_lineZ' g hg] at hmul
  have hcard : Nat.card (Fin n → ZMod p) = p ^ n := by
    simp [Nat.card_eq_fintype_card, ZMod.card]
  rw [hcard] at hmul
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [pow_succ, mul_comm (p ^ m) p] at hmul
  simp only [Nat.add_sub_cancel]
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (NeZero.ne p)) hmul

/-- **The index of Construction A in `ℤⁿ` is `p^{n-1}`.** -/
theorem index_latZ [Fact (Nat.Prime p)] (hn : 1 ≤ n) (g : Fin n → ZMod p) (hg : g ≠ 0) :
    (latZ p n g).toAddSubgroup.index = p ^ (n - 1) := by
  have : NeZero p := ⟨(Fact.out (p := Nat.Prime p)).ne_zero⟩
  rw [← index_lineZ hn g hg]
  exact AddSubgroup.index_comap_of_surjective (lineZ g).toAddSubgroup
    (f := (redLin p n).toAddMonoidHom) redLin_surjective

/-! ### Transport to `ℝⁿ` -/

/-- `toReal` as a `ℤ`-linear equivalence onto the standard integer lattice of `ℝⁿ`. -/
noncomputable def toRealEquiv (n : ℕ) : (Fin n → ℤ) ≃ₗ[ℤ] (intLat n) :=
  (LinearEquiv.ofInjective (toReal n) toReal_injective).trans
    (LinearEquiv.ofEq _ _ (intLat_eq_range n).symm)

theorem toRealEquiv_coe (n : ℕ) (y : Fin n → ℤ) : ((toRealEquiv n y : Fin n → ℝ)) = toReal n y :=
  rfl

theorem toReal_mem_latR_iff (g : Fin n → ZMod p) (y : Fin n → ℤ) :
    toReal n y ∈ latR p n g ↔ y ∈ latZ p n g := by
  constructor
  · rintro ⟨z, hz, hzy⟩
    rwa [toReal_injective hzy] at hz
  · intro hy
    exact ⟨y, hy, rfl⟩

theorem comap_addSubgroupOf (g : Fin n → ZMod p) :
    AddSubgroup.comap (toRealEquiv n).toAddEquiv.toAddMonoidHom
        ((latR p n g).toAddSubgroup.addSubgroupOf (intLat n).toAddSubgroup)
      = (latZ p n g).toAddSubgroup := by
  ext y
  simp only [AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup]
  exact toReal_mem_latR_iff g y

/-- **The relative index of `Λ(g)` in `ℤⁿ ⊆ ℝⁿ` is `p^{n-1}`.** -/
theorem relIndex_latR [Fact (Nat.Prime p)] (hn : 1 ≤ n) (g : Fin n → ZMod p) (hg : g ≠ 0) :
    (latR p n g).toAddSubgroup.relIndex (intLat n).toAddSubgroup = p ^ (n - 1) := by
  have hsurj : Function.Surjective ⇑(toRealEquiv n).toAddEquiv.toAddMonoidHom :=
    (toRealEquiv n).toAddEquiv.surjective
  rw [AddSubgroup.relIndex,
    ← AddSubgroup.index_comap_of_surjective
        ((latR p n g).toAddSubgroup.addSubgroupOf (intLat n).toAddSubgroup) hsurj,
    comap_addSubgroupOf g, index_latZ hn g hg]

/-! ### The covolume -/

/-- A `ℤ`-basis of the standard integer lattice of `ℝⁿ`. -/
noncomputable def intLatBasis (n : ℕ) : Module.Basis (Fin n) ℤ (intLat n) :=
  (Pi.basisFun ℤ (Fin n)).map (toRealEquiv n)

theorem covolume_intLat (n : ℕ) : ZLattice.covolume (intLat n) = 1 := by
  classical
  rw [ZLattice.covolume_eq_det (intLat n) (intLatBasis n)]
  have : (Matrix.of ((↑) ∘ (intLatBasis n))) = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simp [intLatBasis, toRealEquiv_coe, toReal_apply, Pi.basisFun_apply, Pi.single_apply,
      Matrix.one_apply, eq_comm]
  rw [this, Matrix.det_one, abs_one]

/-- **The covolume of Construction A.** `covol Λ(g) = p^{n-1}`. -/
theorem covolume_latR [Fact (Nat.Prime p)] (hn : 1 ≤ n) (g : Fin n → ZMod p) (hg : g ≠ 0) :
    ZLattice.covolume (latR p n g) = (p : ℝ) ^ (n - 1) := by
  have h := ZLattice.covolume_div_covolume_eq_relIndex (latR p n g) (intLat n)
    (latR_le_intLat g)
  rw [covolume_intLat, div_one, relIndex_latR hn g hg] at h
  rw [h]
  push_cast
  ring


/-! ### Bridge between the counting and the lattice -/

/-- Membership in Construction A is exactly the incidence relation counted above. -/
theorem mem_latZ_iff_onLine (g : Fin n → ZMod p) (y : Fin n → ℤ) :
    y ∈ latZ p n g ↔ OnLine g (redMod p y) := mem_latZ g y

end Submission.L10.ConstructionA

import Mathlib

/-!
# Gate L-10 (`klartag_packing`) — the discrete chain: architecture

Brief 7.  This module is the **structural** half of hinge 1's discrete replacement for Klartag's
stochastically evolving ellipsoid (arXiv:2504.05042, §2, Proposition 2.3): the process as a Lean
definition, the freezing step, the dimension-drop lemma, the freeze count, adaptedness, and the
invariant `A_k ∈ K_L`.  No probability enters here — every theorem below holds for an *arbitrary*
driving sequence `ξ : ℕ → Ω → E`; the Gaussian law is consumed only by the drift accounting
(`Submission/L10/ChainDrift.lean`), where it appears as named hypotheses.

## The ambient space (rule 7: generic over pinned)

Klartag works in `ℝ^{n×n}_sym` with the Frobenius inner product, and the constraints are the
rank-one matrices `x ⊗ x` for lattice points `x`.  Nothing in §2 uses more than:

* a real inner product space `E` (the symmetric matrices);
* a family `q : ι → E` of constraint vectors (the `x ⊗ x`);
* **non-negative correlation** `0 ≤ ⟪q i, q j⟫` — which for `q x = x ⊗ x` is
  `⟪x ⊗ x, y ⊗ y⟫ = (x ⬝ᵥ y)^2 ≥ 0` (`inner_vecMulVec_self_nonneg` below).

So everything is stated for `E`, `q`, and a finite window `W : Finset ι`.

## The chain

`C₀ = ∅`, `A₀ = a₀ • 1`.  At step `k`, with `F_k = freeSub q C_k` the *free subspace* (the
matrices annihilating every active constraint) and `π_k = starProjection F_k`:

  `A'_{k+1} = A_k + π_k ξ_k`,  `V_{k+1} = {i ∈ W : ⟪A'_{k+1}, q i⟫ < 1}` (newly violated),
  `A_{k+1} = A'_{k+1} + ∑_{i ∈ V} ((1 - ⟪A'_{k+1}, q i⟫)/‖q i‖²) • q i`,  `C_{k+1} = C_k ∪ V`.

**The correction is the explicit one-sided lift, not the Frobenius projection onto `K_L`.**  Both
land in `K_L` and both are `O(√h)` away from `A'`; the lift is used because its log-det cost is
`∑_{i∈V} λ_i ⟪A'⁻¹ x_i, x_i⟫`, with no `‖A'⁻¹‖_F = Θ(√n)` factor — see the report, §5.  The
Frobenius projection is nevertheless developed in full (`IsProjOn`), since the brief asks for it
and since `lift_dist_le` is proved by comparing the two.

## Main results

* `convex_kSet`, `isClosed_kSet`, `exists_isProjOn`, `IsProjOn.eq`, `IsProjOn.norm_sub_le`,
  `IsProjOn.dist_le` — `P_{K_L}` is well defined (exists, unique) and 1-Lipschitz.
* `lift_mem_kSet` — the one-sided lift lands in `K_L`; hence `chainState_mem_kSet`.
* `starProjection_ne_zero_of_violated` — **hinge 1's one linear-algebra line**: a newly violated
  constraint is not orthogonal to the free subspace.
* `freeSub_lt_of_starProjection_ne_zero`, `finrank_freeSub_lt` — the dimension-drop lemma.
* `card_freezes_le` — at most `finrank E` freezes.
* `measurable_chain`, `adapted_chain` — measurability and adaptedness of every object.
-/

set_option linter.unusedSectionVars false

namespace Submission.L10.Chain

open scoped RealInnerProductSpace
open Module Submodule Finset Metric

section Basic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*}

/-! ## 1. The constraint set `K_L` -/

/-- `kSet q W = {A | ∀ i ∈ W, 1 ≤ ⟪A, q i⟫}`.  With `q x = x ⊗ x` this is Klartag's set of
`L`-free matrices (p. 6, eq. 9): `E_A = {x | ⟪A x, x⟫ < 1}` misses every `x` with `q x` a
constraint. -/
def kSet (q : ι → E) (W : Finset ι) : Set E := {A | ∀ i ∈ W, (1 : ℝ) ≤ ⟪A, q i⟫}

theorem mem_kSet {q : ι → E} {W : Finset ι} {A : E} :
    A ∈ kSet q W ↔ ∀ i ∈ W, (1 : ℝ) ≤ ⟪A, q i⟫ := Iff.rfl

/-- `K_L` is convex: an intersection of half-spaces. -/
theorem convex_kSet (q : ι → E) (W : Finset ι) : Convex ℝ (kSet q W) := by
  intro A hA B hB a b ha hb hab i hi
  have h1 : ⟪a • A + b • B, q i⟫ = a * ⟪A, q i⟫ + b * ⟪B, q i⟫ := by
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  rw [h1]
  nlinarith [hA i hi, hB i hi]

/-- `K_L` is closed: an intersection of closed half-spaces. -/
theorem isClosed_kSet (q : ι → E) (W : Finset ι) : IsClosed (kSet q W) := by
  have : kSet q W = ⋂ i ∈ W, (fun A => ⟪A, q i⟫) ⁻¹' (Set.Ici (1 : ℝ)) := by
    ext A; simp [kSet, Set.mem_iInter]
  rw [this]
  refine isClosed_biInter fun i _ => IsClosed.preimage ?_ isClosed_Ici
  exact (continuous_id.inner continuous_const)

/-- If `K_L` is nonempty then no constraint vector vanishes (`⟪A, 0⟫ = 0 < 1`). -/
theorem q_ne_zero_of_nonempty {q : ι → E} {W : Finset ι} {A : E} (hA : A ∈ kSet q W)
    {i : ι} (hi : i ∈ W) : q i ≠ 0 := by
  intro h
  have := hA i hi
  rw [h, inner_zero_right] at this
  linarith

/-! ## 2. The Frobenius projection onto `K_L`

Mathlib has the Hilbert projection theorem for a closed convex set
(`exists_norm_eq_iInf_of_complete_convex`) and its variational characterisation
(`norm_eq_iInf_iff_real_inner_le_zero`) but no packaged projection map.  Following rule 7 we do
not introduce one: `IsProjOn K u p` *is* the variational characterisation, and existence,
uniqueness and the 1-Lipschitz bound are theorems about it. -/

/-- `p` is *the* projection of `u` onto `K`: `p ∈ K` and `K` lies in the half-space through `p`
orthogonal to `u - p`. -/
def IsProjOn (K : Set E) (u p : E) : Prop := p ∈ K ∧ ∀ w ∈ K, ⟪u - p, w - p⟫ ≤ (0 : ℝ)

theorem IsProjOn.mem {K : Set E} {u p : E} (h : IsProjOn K u p) : p ∈ K := h.1

/-- The projection onto a closed convex set exists. -/
theorem exists_isProjOn [FiniteDimensional ℝ E] {K : Set E} (hne : K.Nonempty)
    (hcl : IsClosed K) (hconv : Convex ℝ K) (u : E) : ∃ p, IsProjOn K u p := by
  obtain ⟨p, hpK, hp⟩ := exists_norm_eq_iInf_of_complete_convex hne hcl.isComplete hconv u
  exact ⟨p, hpK, (norm_eq_iInf_iff_real_inner_le_zero hconv hpK).1 hp⟩

/-- The projection onto a convex set is unique. -/
theorem IsProjOn.eq {K : Set E} {u p p' : E} (h : IsProjOn K u p) (h' : IsProjOn K u p') :
    p = p' := by
  have h1 : ⟪u - p, p' - p⟫ ≤ (0 : ℝ) := h.2 _ h'.1
  have h2 : ⟪u - p', p - p'⟫ ≤ (0 : ℝ) := h'.2 _ h.1
  have hid : ⟪p' - p, p' - p⟫ = ⟪u - p, p' - p⟫ + ⟪u - p', p - p'⟫ := by
    simp only [inner_sub_left, inner_sub_right]
    linarith [real_inner_comm u p, real_inner_comm u p', real_inner_comm p p']
  rw [real_inner_self_eq_norm_sq] at hid
  have hz : ‖p' - p‖ = 0 := by nlinarith [norm_nonneg (p' - p)]
  exact (sub_eq_zero.1 (norm_eq_zero.1 hz)).symm

/-- The projection is the nearest point of `K`. -/
theorem IsProjOn.norm_sub_le {K : Set E} {u p w : E} (h : IsProjOn K u p) (hw : w ∈ K) :
    ‖u - p‖ ≤ ‖u - w‖ := by
  have h1 : ⟪u - p, w - p⟫ ≤ (0 : ℝ) := h.2 w hw
  have hexp : ‖u - w‖ ^ 2 = ‖u - p‖ ^ 2 - 2 * ⟪u - p, w - p⟫ + ‖w - p‖ ^ 2 := by
    have hrw : u - w = (u - p) - (w - p) := by abel
    rw [hrw, @norm_sub_sq_real]
  nlinarith [norm_nonneg (u - p), norm_nonneg (u - w), sq_nonneg ‖w - p‖]

/-- A point of `K` is its own projection. -/
theorem IsProjOn.self {K : Set E} {u : E} (hu : u ∈ K) : IsProjOn K u u := by
  refine ⟨hu, fun w _ => ?_⟩
  simp

/-- **The projection onto a convex set is 1-Lipschitz.** -/
theorem IsProjOn.dist_le {K : Set E} {u v p r : E} (hp : IsProjOn K u p) (hr : IsProjOn K v r) :
    ‖p - r‖ ≤ ‖u - v‖ := by
  have h1 : ⟪u - p, r - p⟫ ≤ (0 : ℝ) := hp.2 _ hr.1
  have h2 : ⟪v - r, p - r⟫ ≤ (0 : ℝ) := hr.2 _ hp.1
  have hid : ⟪p - r, p - r⟫ - ⟪u - v, p - r⟫ = ⟪u - p, r - p⟫ + ⟪v - r, p - r⟫ := by
    simp only [inner_sub_left, inner_sub_right]
    linarith [real_inner_comm u p, real_inner_comm u r, real_inner_comm v p,
      real_inner_comm v r, real_inner_comm p r]
  rw [real_inner_self_eq_norm_sq] at hid
  have key : ‖p - r‖ ^ 2 ≤ ⟪u - v, p - r⟫ := by linarith
  rcases eq_or_lt_of_le (norm_nonneg (p - r)) with hzero | hpos
  · rw [← hzero]; exact norm_nonneg _
  · nlinarith [real_inner_le_norm (u - v) (p - r)]

end Basic

section Free

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*}

/-! ## 3. The free subspace and the dimension-drop lemma

`freeSub q C` is Klartag's `F_A` (p. 7, eq. 13): the matrices that annihilate every active
constraint.  The whole six-page construction of §2 (Lemmas 2.1, 2.2, Proposition 2.3) collapses
to `starProjection_ne_zero_of_violated` plus `finrank_freeSub_lt` below. -/

/-- The **free subspace** `F(C) = {B | ∀ i ∈ C, ⟪B, q i⟫ = 0}` (Klartag eq. 13). -/
def freeSub (q : ι → E) (C : Finset ι) : Submodule ℝ E where
  carrier := {B | ∀ i ∈ C, ⟪B, q i⟫ = (0 : ℝ)}
  add_mem' := by
    intro a b ha hb i hi
    rw [inner_add_left, ha i hi, hb i hi, add_zero]
  zero_mem' := by intro i _; rw [inner_zero_left]
  smul_mem' := by
    intro c a ha i hi
    rw [real_inner_smul_left, ha i hi, mul_zero]

@[simp] theorem mem_freeSub {q : ι → E} {C : Finset ι} {B : E} :
    B ∈ freeSub q C ↔ ∀ i ∈ C, ⟪B, q i⟫ = (0 : ℝ) := Iff.rfl

/-- More constraints, smaller free subspace. -/
theorem freeSub_mono {q : ι → E} {C D : Finset ι} (h : C ⊆ D) : freeSub q D ≤ freeSub q C :=
  fun _ hB i hi => hB i (h hi)

/-- `F(C)` is the orthogonal complement of the span of the active constraints. -/
theorem freeSub_eq_orthogonal (q : ι → E) (C : Finset ι) :
    freeSub q C = (span ℝ (q '' (C : Set ι)))ᗮ := by
  ext B
  rw [mem_freeSub, Submodule.mem_orthogonal]
  constructor
  · intro hB u hu
    induction hu using Submodule.span_induction with
    | mem x hx => obtain ⟨i, hi, rfl⟩ := hx; rw [real_inner_comm]; exact hB i hi
    | zero => rw [inner_zero_left]
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul c x _ hx => rw [real_inner_smul_left, hx, mul_zero]
  · intro hB i hi
    rw [real_inner_comm]
    exact hB (q i) (Submodule.subset_span ⟨i, hi, rfl⟩)

variable [FiniteDimensional ℝ E]

/-- `⟪π_C v, v⟫ = ‖π_C v‖²` for the orthogonal projection `π_C` onto `F(C)`. -/
theorem inner_starProjection_self (K : Submodule ℝ E) (v : E) :
    ⟪K.starProjection v, v⟫ = ‖K.starProjection v‖ ^ 2 := by
  have h := K.starProjection_inner_eq_zero v (K.starProjection v) (K.starProjection_apply_mem v)
  rw [inner_sub_left, sub_eq_zero] at h
  rw [real_inner_comm, h, real_inner_self_eq_norm_sq]

/-- **Hinge 1's one linear-algebra line.**  If `A` satisfies every constraint of the window and
the increment `B` lies in the free subspace of `C`, then a constraint `j` that the stepped matrix
`A + B` *violates* cannot be orthogonal to `F(C)`: otherwise the step could not move
`⟪·, q j⟫` at all.  This replaces Lemma 2.1(A)'s compactness argument and Lemma 2.2's
"Brownian motion is unbounded below" argument (Klartag pp. 6-8). -/
theorem starProjection_ne_zero_of_violated {q : ι → E} {W C : Finset ι} {A x : E}
    (hA : A ∈ kSet q W) {j : ι} (hj : j ∈ W)
    (hviol : ⟪A + (freeSub q C).starProjection x, q j⟫ < (1 : ℝ)) :
    (freeSub q C).starProjection (q j) ≠ 0 := by
  intro hzero
  have hmem : q j ∈ (freeSub q C)ᗮ := (Submodule.starProjection_apply_eq_zero_iff _).1 hzero
  have hperp : ⟪(freeSub q C).starProjection x, q j⟫ = (0 : ℝ) := by
    rw [real_inner_comm]
    exact (Submodule.mem_orthogonal' _ _).1 hmem _ ((freeSub q C).starProjection_apply_mem x)
  rw [inner_add_left, hperp, add_zero] at hviol
  exact absurd (hA j hj) (not_le.2 hviol)

section Drop
variable [DecidableEq ι]

/-- **The dimension-drop lemma.**  Adjoining a constraint whose projection into the free subspace
is non-zero strictly shrinks the free subspace. -/
theorem freeSub_lt_of_starProjection_ne_zero {q : ι → E} {C : Finset ι} {j : ι}
    (hj : (freeSub q C).starProjection (q j) ≠ 0) :
    freeSub q (insert j C) < freeSub q C := by
  refine lt_of_le_of_ne (freeSub_mono (Finset.subset_insert _ _)) ?_
  intro heq
  set B := (freeSub q C).starProjection (q j) with hB
  have hBmem : B ∈ freeSub q C := (freeSub q C).starProjection_apply_mem (q j)
  have hBmem' : B ∈ freeSub q (insert j C) := heq ▸ hBmem
  have h1 : ⟪B, q j⟫ = (0 : ℝ) := hBmem' j (Finset.mem_insert_self _ _)
  have h2 : ⟪B, q j⟫ = ‖B‖ ^ 2 := inner_starProjection_self _ _
  exact hj (norm_eq_zero.1 (by nlinarith [norm_nonneg B] : ‖B‖ = 0))

/-- The dimension-drop lemma, in `finrank` form. -/
theorem finrank_freeSub_lt {q : ι → E} {C : Finset ι} {j : ι}
    (hj : (freeSub q C).starProjection (q j) ≠ 0) :
    finrank ℝ (freeSub q (insert j C)) < finrank ℝ (freeSub q C) :=
  Submodule.finrank_lt_finrank_of_lt (freeSub_lt_of_starProjection_ne_zero hj)

end Drop

/-- `dim F(C) ≥ dim E - |q(C)|`: Klartag's `N_t ≥ n(n+1)/2 - |∂E_t ∩ L|/2` (p. 16).  Counting
the *image* `q '' C` rather than `C` itself is what supplies the paper's factor `1/2`, since
`q x = x ⊗ x = q (-x)` identifies the antipodal pairs of contact points. -/
theorem finrank_freeSub_ge (q : ι → E) (C : Finset ι) :
    finrank ℝ E - (q '' (C : Set ι)).ncard ≤ finrank ℝ (freeSub q C) := by
  classical
  have himg : q '' (C : Set ι) = ((C.image q : Finset E) : Set E) := by
    rw [Finset.coe_image]
  have hcard : (q '' (C : Set ι)).ncard = (C.image q).card := by
    rw [himg, Set.ncard_coe_finset]
  have hspan : finrank ℝ (span ℝ (q '' (C : Set ι))) ≤ (C.image q).card := by
    rw [himg]; exact finrank_span_finset_le_card (C.image q)
  have hadd : finrank ℝ (span ℝ (q '' (C : Set ι)))
      + finrank ℝ (span ℝ (q '' (C : Set ι)))ᗮ = finrank ℝ E :=
    Submodule.finrank_add_finrank_orthogonal _
  rw [freeSub_eq_orthogonal, hcard]
  omega

/-- The crude form of `finrank_freeSub_ge`, without the antipodal saving. -/
theorem finrank_freeSub_ge_card (q : ι → E) (C : Finset ι) :
    finrank ℝ E - C.card ≤ finrank ℝ (freeSub q C) := by
  have h := finrank_freeSub_ge q C
  have hle : (q '' (C : Set ι)).ncard ≤ C.card := by
    have := Set.ncard_image_le (s := (C : Set ι)) (f := q) C.finite_toSet
    rwa [Set.ncard_coe_finset] at this
  omega

end Free

section Process

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type*} [DecidableEq ι]

/-! ## 4. The freezing step and the chain

`violated q W A'` is the set of window constraints the stepped matrix breaks; `lift q W A'` pushes
it back into `K_L` along the broken constraints.

**Why the lift and not the Frobenius projection.**  Both land in `K_L`.  The lift's correction is
`Δ = ∑_{i ∈ V} λ_i • q i` with `λ_i ≥ 0`, so for `q x = x ⊗ x` it is *positive semi-definite*, and
the concavity bound on its log-det cost reads `⟪(A')⁻¹, Δ⟫ = ∑ λ_i ⟪(A')⁻¹ x_i, x_i⟫ ≤
∑ λ_i ‖x_i‖² / λ_min(A')`, with no Frobenius norm of `(A')⁻¹` — i.e. no factor `√n`.  The abstract
projection admits only `⟪(A')⁻¹, P(A') - A'⟫ ≤ ‖(A')⁻¹‖_F · ‖P(A') - A'‖_F`, which carries that
`√n` and (report §5) costs a factor `n` of head-room in the step size. -/

/-- The window constraints broken by `A'`. -/
noncomputable def violated (q : ι → E) (W : Finset ι) (A' : E) : Finset ι :=
  W.filter (fun i => ⟪A', q i⟫ < (1 : ℝ))

theorem mem_violated {q : ι → E} {W : Finset ι} {A' : E} {i : ι} :
    i ∈ violated q W A' ↔ i ∈ W ∧ ⟪A', q i⟫ < (1 : ℝ) := by
  simp [violated]

theorem violated_subset (q : ι → E) (W : Finset ι) (A' : E) : violated q W A' ⊆ W :=
  Finset.filter_subset _ _

/-- The **one-sided lift** back into `K_L`: move along the broken constraints only, each by
exactly the amount that makes it tight. -/
noncomputable def lift (q : ι → E) (W : Finset ι) (A' : E) : E :=
  A' + ∑ i ∈ violated q W A', ((1 - ⟪A', q i⟫) / ‖q i‖ ^ 2) • q i

theorem inner_lift (q : ι → E) (W : Finset ι) (A' : E) (j : ι) :
    ⟪lift q W A', q j⟫ = ⟪A', q j⟫
      + ∑ i ∈ violated q W A', ((1 - ⟪A', q i⟫) / ‖q i‖ ^ 2) * ⟪q i, q j⟫ := by
  rw [lift, inner_add_left, sum_inner]
  congr 1
  exact Finset.sum_congr rfl fun i _ => real_inner_smul_left _ _ _

/-- **The lift lands in `K_L`.**  The only structural input is non-negative correlation of the
constraint vectors, `0 ≤ ⟪q i, q j⟫` — true for `q x = x ⊗ x`, where it is `(x ⬝ᵥ y)² ≥ 0`. -/
theorem lift_mem_kSet {q : ι → E} {W : Finset ι} (A' : E)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0) :
    lift q W A' ∈ kSet q W := by
  intro j hj
  have hcoef : ∀ i ∈ violated q W A', 0 ≤ (1 - ⟪A', q i⟫) / ‖q i‖ ^ 2 := by
    intro i hi
    rcases mem_violated.1 hi with ⟨hiW, hilt⟩
    exact div_nonneg (by linarith) (sq_nonneg _)
  rw [inner_lift]
  by_cases hjV : j ∈ violated q W A'
  · have hqj : ‖q j‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 (hne j hj))
    have hsplit : ∑ i ∈ violated q W A', ((1 - ⟪A', q i⟫) / ‖q i‖ ^ 2) * ⟪q i, q j⟫
        = ((1 - ⟪A', q j⟫) / ‖q j‖ ^ 2) * ⟪q j, q j⟫
          + ∑ i ∈ (violated q W A').erase j, ((1 - ⟪A', q i⟫) / ‖q i‖ ^ 2) * ⟪q i, q j⟫ :=
      (Finset.add_sum_erase _ _ hjV).symm
    have hrest : 0 ≤ ∑ i ∈ (violated q W A').erase j,
        ((1 - ⟪A', q i⟫) / ‖q i‖ ^ 2) * ⟪q i, q j⟫ := by
      refine Finset.sum_nonneg fun i hi => ?_
      have hi' := Finset.mem_of_mem_erase hi
      exact mul_nonneg (hcoef i hi') (hq i (violated_subset q W A' hi') j hj)
    have hdiag : ((1 - ⟪A', q j⟫) / ‖q j‖ ^ 2) * ⟪q j, q j⟫ = 1 - ⟪A', q j⟫ := by
      rw [real_inner_self_eq_norm_sq, div_mul_cancel₀ _ hqj]
    rw [hsplit, hdiag]
    linarith
  · have h1 : (1 : ℝ) ≤ ⟪A', q j⟫ := by
      by_contra hlt
      exact hjV (mem_violated.2 ⟨hj, not_le.1 hlt⟩)
    have hrest : 0 ≤ ∑ i ∈ violated q W A', ((1 - ⟪A', q i⟫) / ‖q i‖ ^ 2) * ⟪q i, q j⟫ :=
      Finset.sum_nonneg fun i hi =>
        mul_nonneg (hcoef i hi) (hq i (violated_subset q W A' hi) j hj)
    linarith

/-- One step of the chain: Gaussian increment inside the free subspace, then the lift, then the
newly broken constraints are adjoined to the active set. -/
noncomputable def stepTo (q : ι → E) (W : Finset ι) (p : E × Finset ι) (x : E) : E × Finset ι :=
  (lift q W (p.1 + (freeSub q p.2).starProjection x),
    p.2 ∪ violated q W (p.1 + (freeSub q p.2).starProjection x))

/-- **The chain** `(A_k, C_k)`, driven by an arbitrary sequence `ξ`.  Klartag's Proposition 2.3. -/
noncomputable def chain (q : ι → E) (W : Finset ι) (A₀ : E) {Ω : Type*} (ξ : ℕ → Ω → E) :
    ℕ → Ω → E × Finset ι
  | 0, _ => (A₀, ∅)
  | k + 1, ω => stepTo q W (chain q W A₀ ξ k ω) (ξ k ω)

variable {q : ι → E} {W : Finset ι} {A₀ : E} {Ω : Type*} {ξ : ℕ → Ω → E}

@[simp] theorem chain_zero (ω : Ω) : chain q W A₀ ξ 0 ω = (A₀, ∅) := rfl

theorem chain_succ (k : ℕ) (ω : Ω) :
    chain q W A₀ ξ (k + 1) ω = stepTo q W (chain q W A₀ ξ k ω) (ξ k ω) := rfl

/-- **`A_k ∈ K_L` for every `k`** (Klartag Proposition 2.3(C), the `L`-free half). -/
theorem chain_fst_mem_kSet (hA₀ : A₀ ∈ kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0) (k : ℕ) (ω : Ω) :
    (chain q W A₀ ξ k ω).1 ∈ kSet q W := by
  cases k with
  | zero => exact hA₀
  | succ k => exact lift_mem_kSet _ hq hne

/-- The active set only grows (Klartag Proposition 2.3(D)). -/
theorem chain_snd_subset_succ (k : ℕ) (ω : Ω) :
    (chain q W A₀ ξ k ω).2 ⊆ (chain q W A₀ ξ (k + 1) ω).2 := by
  rw [chain_succ]; exact Finset.subset_union_left

theorem chain_snd_mono {k m : ℕ} (h : k ≤ m) (ω : Ω) :
    (chain q W A₀ ξ k ω).2 ⊆ (chain q W A₀ ξ m ω).2 := by
  induction m with
  | zero => rw [Nat.le_zero.1 h]
  | succ m ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le h) with hlt | heq
    · exact (ih (Nat.lt_succ_iff.1 hlt)).trans (chain_snd_subset_succ m ω)
    · rw [heq]

theorem chain_snd_subset_window (k : ℕ) (ω : Ω) : (chain q W A₀ ξ k ω).2 ⊆ W := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [chain_succ, stepTo]
    exact Finset.union_subset ih (violated_subset _ _ _)

end Process

section Freezes

/-! ## 5. The freeze count

Klartag bounds the number of steps of his recursion by `|∂E ∩ L| ≤ 2(2ⁿ - 1)` via Lemma A.1
(p. 10, eq. 30).  The discrete chain gets the sharper and far cheaper bound `dim ℝ^{n×n}_sym`
directly from the dimension drop. -/

/-- A `ℕ`-valued antitone sequence has at most `N 0` strict descents. -/
theorem card_descents_le {N : ℕ → ℕ} (hanti : ∀ k, N (k + 1) ≤ N k) (m : ℕ) :
    ((Finset.range m).filter fun k => N (k + 1) < N k).card + N m ≤ N 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hm : m ∉ (Finset.range m).filter fun k => N (k + 1) < N k := by simp
    have hstep := hanti m
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases h : N (m + 1) < N m
    · rw [ite_eq_left h, Finset.card_insert_of_notMem hm]; omega
    · rw [ite_eq_right h]; omega

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type*} [DecidableEq ι]
variable {q : ι → E} {W : Finset ι} {A₀ : E} {Ω : Type*} {ξ : ℕ → Ω → E}

@[simp] theorem freeSub_empty (q : ι → E) : freeSub q (∅ : Finset ι) = ⊤ := by
  ext B; simp

/-- `N_k = dim F(C_k)`, Klartag's `N_t` (p. 13, eq. 39). -/
noncomputable def freeDim (q : ι → E) (W : Finset ι) (A₀ : E) (ξ : ℕ → Ω → E) (k : ℕ) (ω : Ω) :
    ℕ :=
  finrank ℝ (freeSub q (chain q W A₀ ξ k ω).2)

theorem freeDim_zero (ω : Ω) : freeDim q W A₀ ξ 0 ω = finrank ℝ E := by
  rw [freeDim, chain_zero, freeSub_empty, finrank_top]

theorem freeDim_antitone (k : ℕ) (ω : Ω) :
    freeDim q W A₀ ξ (k + 1) ω ≤ freeDim q W A₀ ξ k ω :=
  Submodule.finrank_mono (freeSub_mono (chain_snd_subset_succ k ω))

/-- `k` is a **freeze** step for `ω`: the active set grows. -/
def Freezes (q : ι → E) (W : Finset ι) (A₀ : E) (ξ : ℕ → Ω → E) (k : ℕ) (ω : Ω) : Prop :=
  (chain q W A₀ ξ (k + 1) ω).2 ≠ (chain q W A₀ ξ k ω).2

/-- **Every freeze strictly drops the dimension of the free subspace.** -/
theorem freeDim_lt_of_freezes (hA₀ : A₀ ∈ kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    {k : ℕ} {ω : Ω} (hfz : Freezes q W A₀ ξ k ω) :
    freeDim q W A₀ ξ (k + 1) ω < freeDim q W A₀ ξ k ω := by
  set C := (chain q W A₀ ξ k ω).2 with hC
  set A := (chain q W A₀ ξ k ω).1 with hA
  set A' := A + (freeSub q C).starProjection (ξ k ω) with hA'
  have hnext : (chain q W A₀ ξ (k + 1) ω).2 = C ∪ violated q W A' := rfl
  have hexists : ∃ j ∈ violated q W A', j ∉ C := by
    by_contra hcon
    refine hfz ?_
    rw [hnext, Finset.union_eq_left.2 (fun j hj => by
      by_contra hjc
      exact hcon ⟨j, hj, hjc⟩)]
  obtain ⟨j, hjV, hjC⟩ := hexists
  obtain ⟨hjW, hjlt⟩ := mem_violated.1 hjV
  have hkey : (freeSub q C).starProjection (q j) ≠ 0 :=
    starProjection_ne_zero_of_violated (chain_fst_mem_kSet hA₀ hq hne k ω) hjW hjlt
  have hins : insert j C ⊆ (chain q W A₀ ξ (k + 1) ω).2 := by
    rw [hnext]
    exact Finset.insert_subset (Finset.mem_union_right _ hjV) Finset.subset_union_left
  calc finrank ℝ (freeSub q (chain q W A₀ ξ (k + 1) ω).2)
      ≤ finrank ℝ (freeSub q (insert j C)) := Submodule.finrank_mono (freeSub_mono hins)
    _ < finrank ℝ (freeSub q C) := finrank_freeSub_lt hkey

/-- **At most `dim E` freezes.**  For `E = ℝ^{n×n}_sym` this is `n(n+1)/2`, replacing the
paper's `2(2ⁿ - 1)`. -/
theorem card_freezes_le (hA₀ : A₀ ∈ kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0)
    (m : ℕ) (ω : Ω) [DecidablePred fun k => Freezes q W A₀ ξ k ω] :
    ((Finset.range m).filter fun k => Freezes q W A₀ ξ k ω).card + freeDim q W A₀ ξ m ω
      ≤ finrank ℝ E := by
  classical
  have hsub : ((Finset.range m).filter fun k => Freezes q W A₀ ξ k ω)
      ⊆ (Finset.range m).filter fun k =>
        freeDim q W A₀ ξ (k + 1) ω < freeDim q W A₀ ξ k ω := by
    intro k hk
    rw [Finset.mem_filter] at hk ⊢
    exact ⟨hk.1, freeDim_lt_of_freezes hA₀ hq hne hk.2⟩
  have hcount := card_descents_le (N := fun k => freeDim q W A₀ ξ k ω)
    (fun k => freeDim_antitone k ω) m
  rw [freeDim_zero] at hcount
  have := Finset.card_le_card hsub
  omega

end Freezes

section NewActive

/-! ## 5b. The newly-active blocks

A step can only break constraints that are **not already active**: the increment lies in
`F(C_k)`, which annihilates every active constraint, so `⟪A'_{k+1}, q i⟫ = ⟪A_k, q i⟫ ≥ 1` for
`i ∈ C_k`.  Hence the active set grows by *disjoint* blocks and `∑_{k<m} |V_k| = |C_m|`.

This is what the discretisation-error accounting sums over: the total log-det cost of the
corrections is `∑_k ∑_{i ∈ V_k} λ_i ⟪(A'_{k+1})⁻¹ x_i, x_i⟫`, with `∑_k |V_k| = |C_m|` terms, not
`(number of freezes) × (worst block size)`. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type*} [DecidableEq ι]
variable {q : ι → E} {W : Finset ι} {A₀ : E} {Ω : Type*} {ξ : ℕ → Ω → E}

/-- `V_{k+1}`: the constraints newly broken at step `k`. -/
noncomputable def newActive (q : ι → E) (W : Finset ι) (A₀ : E) (ξ : ℕ → Ω → E) (k : ℕ) (ω : Ω) :
    Finset ι :=
  violated q W ((chain q W A₀ ξ k ω).1
    + (freeSub q (chain q W A₀ ξ k ω).2).starProjection (ξ k ω))

theorem chain_snd_succ_eq (k : ℕ) (ω : Ω) :
    (chain q W A₀ ξ (k + 1) ω).2 = (chain q W A₀ ξ k ω).2 ∪ newActive q W A₀ ξ k ω := rfl

/-- **A step breaks no already-active constraint.** -/
theorem violated_disjoint {C : Finset ι} {A x : E} (hA : A ∈ kSet q W) :
    Disjoint (violated q W (A + (freeSub q C).starProjection x)) C := by
  rw [Finset.disjoint_left]
  intro i hiV hiC
  obtain ⟨hiW, hilt⟩ := mem_violated.1 hiV
  have hperp : ⟪(freeSub q C).starProjection x, q i⟫ = (0 : ℝ) :=
    (mem_freeSub.1 ((freeSub q C).starProjection_apply_mem x)) i hiC
  rw [inner_add_left, hperp, add_zero] at hilt
  exact absurd (hA i hiW) (not_le.2 hilt)

theorem newActive_disjoint (hA₀ : A₀ ∈ kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0) (k : ℕ) (ω : Ω) :
    Disjoint (newActive q W A₀ ξ k ω) (chain q W A₀ ξ k ω).2 :=
  violated_disjoint (chain_fst_mem_kSet hA₀ hq hne k ω)

/-- The active set grows by exactly the size of the new block. -/
theorem card_chain_snd_succ (hA₀ : A₀ ∈ kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0) (k : ℕ) (ω : Ω) :
    (chain q W A₀ ξ (k + 1) ω).2.card
      = (chain q W A₀ ξ k ω).2.card + (newActive q W A₀ ξ k ω).card := by
  rw [chain_snd_succ_eq, Finset.card_union_of_disjoint
    (newActive_disjoint hA₀ hq hne k ω).symm]

/-- **`∑_{k<m} |V_k| = |C_m|`** — the number of terms in the discretisation-error sum. -/
theorem sum_card_newActive (hA₀ : A₀ ∈ kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0) (m : ℕ) (ω : Ω) :
    ∑ k ∈ Finset.range m, (newActive q W A₀ ξ k ω).card = (chain q W A₀ ξ m ω).2.card := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, card_chain_snd_succ hA₀ hq hne m ω]

/-- A freeze is exactly a non-empty new block. -/
theorem freezes_iff (hA₀ : A₀ ∈ kSet q W)
    (hq : ∀ i ∈ W, ∀ j ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (hne : ∀ i ∈ W, q i ≠ 0) (k : ℕ) (ω : Ω) :
    Freezes q W A₀ ξ k ω ↔ (newActive q W A₀ ξ k ω).Nonempty := by
  constructor
  · intro hfz
    rcases Finset.eq_empty_or_nonempty (newActive q W A₀ ξ k ω) with hemp | hne'
    · exact absurd (by rw [chain_snd_succ_eq, hemp, Finset.union_empty]) hfz
    · exact hne'
  · intro ⟨j, hj⟩ heq
    have hcard := card_chain_snd_succ (ξ := ξ) hA₀ hq hne k ω
    rw [heq] at hcard
    have : 0 < (newActive q W A₀ ξ k ω).card := Finset.card_pos.2 ⟨j, hj⟩
    omega

end NewActive

section Measurability

/-! ## 6. Measurability and adaptedness

The active set is `Finset ι`-valued; it carries the discrete σ-algebra, declared **locally** so
that the exported statements (`measurable_chain_fst`, `measurableSet_mem_active`) mention only the
σ-algebras of `E` and `Ω`. -/

open scoped MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [DecidableEq ι] [Countable ι]
variable {Ω : Type*}

local instance instMeasurableSpaceFinset : MeasurableSpace (Finset ι) := ⊤

local instance instMeasurableSingletonFinset : MeasurableSingletonClass (Finset ι) :=
  ⟨fun _ => trivial⟩

/-- A `Finset`-valued `filter` of measurable predicates is measurable. -/
theorem measurableSet_filter_eq {α : Type*} [MeasurableSpace α] (W s : Finset ι)
    (P : ι → α → Prop) [∀ i, DecidablePred (P i)] (hP : ∀ i, MeasurableSet {a | P i a}) :
    MeasurableSet {a | W.filter (fun i => P i a) = s} := by
  by_cases hs : s ⊆ W
  · have hset : {a | W.filter (fun i => P i a) = s}
        = (⋂ i ∈ (s : Set ι), {a | P i a}) ∩ ⋂ i ∈ ((W \ s : Finset ι) : Set ι), {a | ¬ P i a} := by
      ext a
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Finset.mem_coe,
        Finset.mem_sdiff]
      constructor
      · intro hfilt
        refine ⟨fun i hi => ?_, fun i hi => ?_⟩
        · have : i ∈ W.filter (fun i => P i a) := by rw [hfilt]; exact hi
          exact (Finset.mem_filter.1 this).2
        · intro hPi
          have : i ∈ W.filter (fun i => P i a) := Finset.mem_filter.2 ⟨hi.1, hPi⟩
          rw [hfilt] at this
          exact hi.2 this
      · rintro ⟨h1, h2⟩
        ext i
        rw [Finset.mem_filter]
        constructor
        · rintro ⟨hiW, hPi⟩
          by_contra hik
          exact h2 i ⟨hiW, hik⟩ hPi
        · intro hi
          exact ⟨hs hi, h1 i hi⟩
    rw [hset]
    exact MeasurableSet.inter
      (MeasurableSet.biInter (Finset.countable_toSet s) fun i _ => hP i)
      (MeasurableSet.biInter (Finset.countable_toSet (W \ s)) fun i _ => (hP i).compl)
  · have hset : {a | W.filter (fun i => P i a) = s} = ∅ := by
      ext a
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hfilt
      exact hs (hfilt ▸ Finset.filter_subset _ _)
    rw [hset]
    exact MeasurableSet.empty

variable (q : ι → E) (W : Finset ι)

theorem measurable_violated : Measurable fun A' : E => violated q W A' := by
  classical
  refine measurable_to_countable' fun s => ?_
  have : (fun A' : E => violated q W A') ⁻¹' {s}
      = {A' : E | W.filter (fun i => ⟪A', q i⟫ < (1 : ℝ)) = s} := rfl
  rw [this]
  refine measurableSet_filter_eq W s _ fun i => ?_
  exact measurableSet_lt (by fun_prop) measurable_const

/-- The lift, written as a sum over the whole window: this is the form measurability uses. -/
theorem lift_eq_sum_window (A' : E) :
    lift q W A' = A' + ∑ i ∈ W,
      (if ⟪A', q i⟫ < (1 : ℝ) then (1 - ⟪A', q i⟫) / ‖q i‖ ^ 2 else 0) • q i := by
  rw [lift, violated, Finset.sum_filter]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  split <;> simp

theorem measurable_lift : Measurable fun A' : E => lift q W A' := by
  simp only [lift_eq_sum_window]
  refine measurable_id.add (Finset.measurable_sum W fun i _ => ?_)
  refine Measurable.smul ?_ measurable_const
  exact Measurable.ite (measurableSet_lt (by fun_prop) measurable_const)
    (by fun_prop) measurable_const

theorem measurable_stepTo :
    Measurable fun p : (E × E) × Finset ι => stepTo q W (p.1.1, p.2) p.1.2 := by
  refine measurable_from_prod_countable_left fun C => ?_
  have hA' : Measurable fun p : E × E => p.1 + (freeSub q C).starProjection p.2 :=
    measurable_fst.add (((freeSub q C).starProjection.continuous.measurable).comp measurable_snd)
  exact ((measurable_lift q W).comp hA').prodMk ((measurable_from_top (f := fun s =>
    C ∪ s)).comp ((measurable_violated q W).comp hA'))

variable {q W} {A₀ : E} {ξ : ℕ → Ω → E}

/-- **Adaptedness.**  If `ξ k` is `m (k+1)`-measurable along a monotone family of σ-algebras,
then `(A_k, C_k)` is `m k`-measurable — Klartag Proposition 2.3's "adapted to the filtration". -/
theorem measurable_chain {m : ℕ → MeasurableSpace Ω} (hmono : Monotone m)
    (hξ : ∀ k, Measurable[m (k + 1)] (ξ k)) (k : ℕ) :
    Measurable[m k] fun ω => chain q W A₀ ξ k ω := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    have ih' : Measurable[m (k + 1)] fun ω => chain q W A₀ ξ k ω :=
      ih.mono (hmono (Nat.le_succ k)) le_rfl
    have hpair : Measurable[m (k + 1)] fun ω =>
        (((chain q W A₀ ξ k ω).1, ξ k ω), (chain q W A₀ ξ k ω).2) :=
      ((measurable_fst.comp ih').prodMk (hξ k)).prodMk (measurable_snd.comp ih')
    exact (measurable_stepTo q W).comp hpair

variable [MeasurableSpace Ω]

theorem measurable_chain' (hξ : ∀ k, Measurable (ξ k)) (k : ℕ) :
    Measurable fun ω => chain q W A₀ ξ k ω :=
  measurable_chain (m := fun _ => ‹MeasurableSpace Ω›) monotone_const hξ k

/-- `A_k` is measurable. -/
theorem measurable_chain_fst (hξ : ∀ k, Measurable (ξ k)) (k : ℕ) :
    Measurable fun ω => (chain q W A₀ ξ k ω).1 :=
  measurable_fst.comp (measurable_chain' hξ k)

/-- `{ω | i ∈ C_k ω}` is measurable — the form the contact-count expectation
`E |C_N| = ∑_i P(i ∈ C_N)` consumes. -/
theorem measurableSet_mem_active (hξ : ∀ k, Measurable (ξ k)) (k : ℕ) (i : ι) :
    MeasurableSet {ω | i ∈ (chain q W A₀ ξ k ω).2} := by
  have h : Measurable fun ω => (chain q W A₀ ξ k ω).2 :=
    measurable_snd.comp (measurable_chain' hξ k)
  have h2 : MeasurableSet ((fun ω => (chain q W A₀ ξ k ω).2) ⁻¹' {s : Finset ι | i ∈ s}) :=
    h trivial
  exact h2

end Measurability

end Submission.L10.Chain

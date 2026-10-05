/-
Gate L-10 (`klartag_packing`), brief 44.

**The chain's defining equation, and the containment.**

Report 43 named one missing piece: the identification of the chain's martingale increment with the
padded inner product, "which needs the constraint vectors normalised".  Both halves are here.

* `constraint_walk_eq` — along one step, `⟪A_k, q j⟫` moves by the martingale increment
  `⟪π_k ξ_k, q j⟫` plus the lift term.  This is `Chain.stepTo` unfolded through `Chain.inner_lift`.
* `lift_term_nonneg` — the lift is **one-sided**: a violated constraint has `⟪A', q i⟫ < 1` and the
  constraint vectors are non-negatively correlated (`ChainWiring.inner_qUT_nonneg`: `⟪q x, q y⟫ =
  (x ⬝ᵥ y)²`), so the lift only pushes constraint values up.  Hence the *pure* walk, with the lift
  dropped, stays below the constraint value, and a point that becomes active has already driven the
  pure walk to the boundary — `pureWalk_le_one_of_mem`, the containment.
* `pureWalk_succ_sub` — the increment is `⟪ξ_k, π_k (q j)⟫`, an inner product against a
  past-measurable vector: exactly `PaddingMap.padInc`'s shape.
* `norm_proj_unit_le` — report 43's `‖π_j v_j‖ ≤ 1`, which is just that an orthogonal projection is
  a contraction; `ChainWiring.inner_qUT` gives `‖q x‖ = ‖x‖²`, so `q x/‖q x‖` is the unit vector to
  project.
-/
import Submission.L10.PaddingMap
import Submission.L10.Chain
import Submission.L10.ChainWiring
namespace Submission.L10
open MeasureTheory Set Real Submission.L10.Chain
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type*} [DecidableEq ι] {Ω : Type*}

/-- The **pure** constraint walk: `⟪A₀, q j⟫` plus the martingale increments only, with the
one-sided lift dropped. -/
noncomputable def pureWalk (q : ι → E) (W : Finset ι) (A₀ : E) (ξ : ℕ → Ω → E) (j : ι) :
    ℕ → Ω → ℝ
  | 0, _ => ⟪A₀, q j⟫
  | k + 1, ω => pureWalk q W A₀ ξ j k ω
      + ⟪(freeSub q (chain q W A₀ ξ k ω).2).starProjection (ξ k ω), q j⟫

variable {q : ι → E} {W : Finset ι} {A₀ : E} {ξ : ℕ → Ω → E}

/-- **The chain's defining equation.**  Along one step the constraint value `⟪A_k, q j⟫` moves by
the martingale increment `⟪π_k ξ_k, q j⟫` plus the one-sided lift term. -/
theorem constraint_walk_eq (j : ι) (k : ℕ) (ω : Ω) :
    ⟪(chain q W A₀ ξ (k + 1) ω).1, q j⟫
      = ⟪(chain q W A₀ ξ k ω).1, q j⟫
        + ⟪(freeSub q (chain q W A₀ ξ k ω).2).starProjection (ξ k ω), q j⟫
        + ∑ i ∈ violated q W ((chain q W A₀ ξ k ω).1
              + (freeSub q (chain q W A₀ ξ k ω).2).starProjection (ξ k ω)),
            ((1 - ⟪(chain q W A₀ ξ k ω).1
              + (freeSub q (chain q W A₀ ξ k ω).2).starProjection (ξ k ω), q i⟫)
              / ‖q i‖ ^ 2) * ⟪q i, q j⟫ := by
  rw [chain_succ, stepTo, inner_lift, inner_add_left]

/-- **The lift is one-sided.**  Every summand is non-negative, because a violated constraint has
`⟪A', q i⟫ < 1` and the constraint vectors are non-negatively correlated. -/
theorem lift_term_nonneg (j : ι) (A' : E)
    (hq : ∀ i ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) :
    (0 : ℝ) ≤ ∑ i ∈ violated q W A', ((1 - ⟪A', q i⟫) / ‖q i‖ ^ 2) * ⟪q i, q j⟫ := by
  refine Finset.sum_nonneg fun i hi => ?_
  obtain ⟨hiW, hilt⟩ := mem_violated.1 hi
  exact mul_nonneg (div_nonneg (by linarith) (sq_nonneg _)) (hq i hiW)

/-- **The pure walk is below the constraint value.**  The lift only pushes constraints up. -/
theorem pureWalk_le (j : ι) (hq : ∀ i ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (k : ℕ) (ω : Ω) :
    pureWalk q W A₀ ξ j k ω ≤ ⟪(chain q W A₀ ξ k ω).1, q j⟫ := by
  induction k with
  | zero => exact le_of_eq rfl
  | succ k ih =>
    rw [constraint_walk_eq j k ω]
    have h := lift_term_nonneg (q := q) (W := W) j
      ((chain q W A₀ ξ k ω).1
        + (freeSub q (chain q W A₀ ξ k ω).2).starProjection (ξ k ω)) hq
    show pureWalk q W A₀ ξ j k ω
        + ⟪(freeSub q (chain q W A₀ ξ k ω).2).starProjection (ξ k ω), q j⟫ ≤ _
    linarith

/-- **The containment.**  If `j` is active at step `k`, the *pure* walk has already reached the
boundary `1` by step `k` — so the contact event sits inside the padded walk's hitting event. -/
theorem pureWalk_le_one_of_mem (j : ι) (hq : ∀ i ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) :
    ∀ (k : ℕ) (ω : Ω), j ∈ (chain q W A₀ ξ k ω).2 →
      ∃ i ≤ k, pureWalk q W A₀ ξ j i ω ≤ 1 := by
  intro k
  induction k with
  | zero => intro ω hj; simp at hj
  | succ k ih =>
    intro ω hj
    rw [chain_snd_succ_eq] at hj
    rcases Finset.mem_union.1 hj with h | h
    · obtain ⟨i, hik, hle⟩ := ih ω h
      exact ⟨i, le_trans hik (Nat.le_succ k), hle⟩
    · refine ⟨k + 1, le_rfl, ?_⟩
      obtain ⟨_, hlt⟩ := mem_violated.1 h
      have hdom := pureWalk_le (q := q) (W := W) (A₀ := A₀) (ξ := ξ) j hq k ω
      show pureWalk q W A₀ ξ j k ω
          + ⟪(freeSub q (chain q W A₀ ξ k ω).2).starProjection (ξ k ω), q j⟫ ≤ 1
      rw [inner_add_left] at hlt
      linarith

/-- The pure walk's increment, read against the increment: the projection is self-adjoint, so the
martingale increment is `⟪ξ_k, π_k (q j)⟫` — an inner product against a **past-measurable**
vector, which is what `PaddingMap.padInc` consumes. -/
theorem pureWalk_succ_sub (j : ι) (k : ℕ) (ω : Ω) :
    pureWalk q W A₀ ξ j (k + 1) ω - pureWalk q W A₀ ξ j k ω
      = ⟪ξ k ω, (freeSub q (chain q W A₀ ξ k ω).2).starProjection (q j)⟫ := by
  show (pureWalk q W A₀ ξ j k ω
      + ⟪(freeSub q (chain q W A₀ ξ k ω).2).starProjection (ξ k ω), q j⟫)
    - pureWalk q W A₀ ξ j k ω = _
  rw [add_sub_cancel_left]
  exact (freeSub q (chain q W A₀ ξ k ω).2).starProjection_isSymmetric (ξ k ω) (q j)

omit [FiniteDimensional ℝ E] in
/-- **The normalisation.**  The projected direction of a unit constraint vector has norm at most
one — this is report 43's `‖π_j v_j‖ ≤ 1`, and it is just that an orthogonal projection is a
contraction. -/
theorem norm_proj_unit_le (K : Submodule ℝ E) [K.HasOrthogonalProjection] {v : E} (hv : ‖v‖ = 1) :
    ‖K.starProjection v‖ ≤ 1 := by
  have h := K.norm_starProjection_apply_le v
  rwa [hv] at h

/-! ## 2. The scalar martingale, its initial gap, and the containment in transport shape -/

/-- The chain's scalar martingale for a window point, normalised so that the constraint's
boundary is `0`.  `M_0 = ⟪A₀, q j⟫ − 1` is Klartag's initial gap, eq. (61). -/
noncomputable def constraintM (q : ι → E) (W : Finset ι) (A₀ : E) (ξ : ℕ → Ω → E)
    (j : ι) (k : ℕ) (ω : Ω) : ℝ := pureWalk q W A₀ ξ j k ω - 1

theorem constraintM_zero (j : ι) (ω : Ω) :
    constraintM q W A₀ ξ j 0 ω = ⟪A₀, q j⟫ - 1 := rfl

/-- **The containment, in `TailTransport.tail_at_step_μ`'s shape.** -/
theorem chain_hhit (hq : ∀ j : ι, ∀ i ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫) (k : ℕ) (y : ι) :
    {ω : Ω | y ∈ (chain q W A₀ ξ k ω).2}
      ⊆ {ω : Ω | ∃ i ≤ k, constraintM q W A₀ ξ y i ω ≤ 0} := by
  intro ω hω
  obtain ⟨i, hik, hle⟩ := pureWalk_le_one_of_mem (q := q) (W := W) (A₀ := A₀) (ξ := ξ)
    y (hq y) k ω hω
  exact ⟨i, hik, by simpa [constraintM] using hle⟩

/-- **The initial gap.**  `⟪A₀, q y⟫ > 1` is Klartag's eq. (61); it is what makes `M_0 > 0`, and
hence both `padded_tail_of_increments`' `hM₀` and report 40's time-zero vanishing. -/
theorem chain_hgap {y : ι} (hA₀ : (1 : ℝ) < ⟪A₀, q y⟫) (ω : Ω) :
    0 < constraintM q W A₀ ξ y 0 ω := by
  rw [constraintM_zero]; linarith

/-! ## 3. The per-step tail with nothing left but `hprop`, and `ChainRaw2` from the chain -/

section Assembly

open Submission.L10.Tiling Submission.L10.Section5 Submission.L10.ConstructionA
open Submission.L10.ChainDataInst
open scoped ENNReal

variable {n : ℕ} {Ωc : Type*} [MeasurableSpace Ωc] {P : Measure Ωc} [IsProbabilityMeasure P]
variable {Ec : Type*} [NormedAddCommGroup Ec] [InnerProductSpace ℝ Ec] [FiniteDimensional ℝ Ec]

/-- Abbreviation: the chain's accumulated contact set. -/
noncomputable def contactSet (q : (Fin n → ℤ) → Ec) (W : Finset (Fin n → ℤ)) (A₀ : Ec)
    (ξ : ℕ → Ωc → Ec) (k : ℕ) (ω : Ωc) : Finset (Fin n → ℤ) := (chain q W A₀ ξ k ω).2

variable {q : (Fin n → ℤ) → Ec} {W : Finset (Fin n → ℤ)} {A₀ : Ec} {ξ : ℕ → Ωc → Ec} {α : ℝ}

/-- **The per-step tail, with the containment and time zero discharged from the chain.**  Only
`hprop` — Proposition 4.1 at horizon `k·h`, transported by `TailTransport.hit_tail_yOf` — and the
window conditions remain. -/
theorem hsteps_of_walk
    (hq : ∀ j : (Fin n → ℤ), ∀ i ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫)
    (hA₀ : ∀ y ∈ W, (1 : ℝ) < ⟪A₀, q y⟫)
    (hwin : ∀ y ∈ W, ‖toE n y‖ + Real.sqrt n / 2 ≤ windowC α n)
    (hr : ∀ y ∈ W, 0 < α * ‖toE n y‖)
    (hy : ∀ k, k < ParamsAdopted2.numStepsAdopted2 n → k ≠ 0 → ∀ y ∈ W,
      0 < yOf (a0C n) ((k : ℝ) * ParamsAdopted2.stepSizeAdopted2 n) (α * ‖toE n y‖))
    (hprop : ∀ k, k < ParamsAdopted2.numStepsAdopted2 n → k ≠ 0 → ∀ y ∈ W,
      P {ω | ∃ i ≤ k, constraintM q W A₀ ξ y i ω ≤ 0}
        ≤ ENNReal.ofReal (4 * Phi (yOf (a0C n)
            ((k : ℝ) * ParamsAdopted2.stepSizeAdopted2 n) (α * ‖toE n y‖)))) :
    ∀ k, k < ParamsAdopted2.numStepsAdopted2 n → ∀ y ∈ W,
      P.real {ω | y ∈ contactSet q W A₀ ξ k ω}
        ≤ 4 * profStep α n (ParamsAdopted2.stepSizeAdopted2 n) y k :=
  tail_at_step_μ (contactSet q W A₀ ξ) W (constraintM q W A₀ ξ) hwin hr hy
    (fun k _ y _ => chain_hhit hq k y) hprop
    (contact_zero_of_gap (contactSet q W A₀ ξ) W (constraintM q W A₀ ξ)
      (fun y _ => chain_hhit hq 0 y)
      (fun y hy' ω => chain_hgap (hA₀ y hy') ω))

/-- **`ChainRaw2.tail` from the chain.** -/
theorem tail_of_transport'' (hn : 3 ≤ n) (hα : 0 < α)
    (hq : ∀ j : (Fin n → ℤ), ∀ i ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫)
    (hA₀ : ∀ y ∈ W, (1 : ℝ) < ⟪A₀, q y⟫)
    (hwin : ∀ y ∈ W, ‖toE n y‖ + Real.sqrt n / 2 ≤ windowC α n)
    (hr : ∀ y ∈ W, 0 < α * ‖toE n y‖)
    (hy : ∀ k, k < ParamsAdopted2.numStepsAdopted2 n → k ≠ 0 → ∀ y ∈ W,
      0 < yOf (a0C n) ((k : ℝ) * ParamsAdopted2.stepSizeAdopted2 n) (α * ‖toE n y‖))
    (hprop : ∀ k, k < ParamsAdopted2.numStepsAdopted2 n → k ≠ 0 → ∀ y ∈ W,
      P {ω | ∃ i ≤ k, constraintM q W A₀ ξ y i ω ≤ 0}
        ≤ ENNReal.ofReal (4 * Phi (yOf (a0C n)
            ((k : ℝ) * ParamsAdopted2.stepSizeAdopted2 n) (α * ‖toE n y‖)))) :
    ∀ y ∈ W, ENNReal.ofReal (ContactIntegrated.intWeight P (contactSet q W A₀ ξ)
        (ParamsAdopted2.stepSizeAdopted2 n) (ParamsAdopted2.numStepsAdopted2 n) y)
      ≤ ENNReal.ofReal (4 * ∫ t in Ioc (0 : ℝ) (ChainDrift.horizon n),
          profileAt (a0C n) α (windowC α n) n t ‖toE n y‖) :=
  fun y hy' => tail_of_steps hn hα (contactSet q W A₀ ξ)
    (fun k hk => hsteps_of_walk hq hA₀ hwin hr hy hprop k hk y hy')

/-- **The terminal per-point tail**, the horizon-`N` instance.  With `weight y := 2·profileAt …
(N·h) ‖toE n y‖` and `err := 0`, this is `ChainDataInst.expected_card_le`'s `htail`, so its
`θ = ∑_{y ∈ W} weight y` and `E = 0`; report 39 records that the drift consumes the *integrated*
count instead, so this is the terminal reading, not the one in use. -/
theorem terminal_tail {N : ℕ} {hstep : ℝ}
    (hq : ∀ j : (Fin n → ℤ), ∀ i ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫)
    (hwin : ∀ y ∈ W, ‖toE n y‖ + Real.sqrt n / 2 ≤ windowC α n)
    (hr : ∀ y ∈ W, 0 < α * ‖toE n y‖)
    (hyN : ∀ y ∈ W, 0 < yOf (a0C n) ((N : ℝ) * hstep) (α * ‖toE n y‖))
    (hpropN : ∀ y ∈ W, P {ω | ∃ i ≤ N, constraintM q W A₀ ξ y i ω ≤ 0}
      ≤ ENNReal.ofReal (4 * Phi (yOf (a0C n) ((N : ℝ) * hstep) (α * ‖toE n y‖)))) :
    ∀ y ∈ W, P.real {ω | y ∈ contactSet q W A₀ ξ N ω}
      ≤ 4 * profileAt (a0C n) α (windowC α n) n ((N : ℝ) * hstep) ‖toE n y‖ := by
  intro y hy'
  rw [profileAt_eq_Phi (hwin y hy') (hr y hy') (hyN y hy')]
  refine measureReal_le_of_le (by
    have := Phi_nonneg (hyN y hy'); linarith) ?_
  exact le_trans (measure_mono (chain_hhit hq N y)) (hpropN y hy')

/-- **`ChainRaw2` from the chain**, with `w = intWeight` and `tail` discharged.  The thirteen
remaining arguments are §5 arithmetic and the chain's own lattice data. -/
noncomputable def chainRaw2_of_walk {p : ℕ} (hn : 3 ≤ n)
    (hq : ∀ j : (Fin n → ℤ), ∀ i ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫)
    (hA₀ : ∀ y ∈ W, (1 : ℝ) < ⟪A₀, q y⟫)
    (alpha_pos : 0 < α)
    (alpha_norm : α ^ n * ((p ^ (n - 1) : ℕ) : ℝ) = kappa n)
    (R : ℝ) (R_nonneg : 0 ≤ R) (R_scaled : α * R ≤ 1 - 1 / (n : ℝ)) (R_lt_p : R < (p : ℝ))
    (tiling_defect : (n : ℝ) * (α * Real.sqrt n / 2) ≤ 1 / 4)
    (window_lt_p : windowC α n < (p : ℝ))
    (supp_ne_zero : ∀ y ∈ W, y ≠ 0)
    (supp_radius : ∀ y ∈ W, ‖toE n y‖ ≤ windowC α n)
    (hwin : ∀ y ∈ W, ‖toE n y‖ + Real.sqrt n / 2 ≤ windowC α n)
    (hr : ∀ y ∈ W, 0 < α * ‖toE n y‖)
    (hy : ∀ k, k < ParamsAdopted2.numStepsAdopted2 n → k ≠ 0 → ∀ y ∈ W,
      0 < yOf (a0C n) ((k : ℝ) * ParamsAdopted2.stepSizeAdopted2 n) (α * ‖toE n y‖))
    (hprop : ∀ k, k < ParamsAdopted2.numStepsAdopted2 n → k ≠ 0 → ∀ y ∈ W,
      P {ω | ∃ i ≤ k, constraintM q W A₀ ξ y i ω ≤ 0}
        ≤ ENNReal.ofReal (4 * Phi (yOf (a0C n)
            ((k : ℝ) * ParamsAdopted2.stepSizeAdopted2 n) (α * ‖toE n y‖))))
    (arith : (n : ℝ) * kappa n * ((p : ℝ) - 1) * (8 - 8 / (n : ℝ) ^ 2)
      < 8 * ((p : ℝ) ^ n - 1)) :
    ChainRaw2 p n :=
  chainRaw2_of_chain (μ := P) hn (contactSet q W A₀ ξ) α alpha_pos alpha_norm R R_nonneg
    R_scaled R_lt_p tiling_defect window_lt_p W supp_ne_zero supp_radius
    (fun y hy' k hk => hsteps_of_walk hq hA₀ hwin hr hy hprop k hk y hy') arith

end Assembly

end Submission.L10

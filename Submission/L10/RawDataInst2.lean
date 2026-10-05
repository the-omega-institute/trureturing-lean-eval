import Mathlib
import Submission.L10.RawDataInst
import Submission.L10.TailSideSetup2
import Submission.L10.ChainWiring

/-!
# Gate L-10 — the chain's `q`, `W`, `A₀`, and HOLE 52 closed

Brief 61, second pass.  `RawDataInst.lean` is reported and is not edited (rule 5); this module
adds what report 61 §3 wrongly said did not exist.

**Correction to report 61 §3.**  That report claimed `q` has no definition in the tree.  It does:
`ChainWiring.qUT` (`:68`), with `inner_qUT_nonneg` (`:101`) — which *is* `RawData.hq` — and
`inner_qUT_eq_quad` (`:84`).  The grep behind the claim searched `def qOf`, `def qMap`,
`vecMulVec`, `def qC` and the binders `hq :`, `hA₀ :`, and matched none of them.  `A₀` and `W`
genuinely had no definition, and are built here.

## What is built

* `idUT`, `symMat_idUT`, `inner_idUT` — the identity in Frobenius coordinates, so that
  `A0C n = a0C n • idUT n` satisfies `⟪A₀, qUT x⟫ = a₀·|x|²`.
* `xOf`, `qC`, `norm_qC`, `inner_A0C_qC`, `normData_qC` — the chain's `q y = qUT (α·toE y)` and
  both fields of `TailSideSetup2.NormData`, for **any** `W`.
* `shell` — the window: integer points with `(1−1/n)/α < ‖toE y‖ ≤ windowC α n − √n/2`.  The
  **inner** radius is what `hA₀` and `hy` need; `RawData` never states it (report 61 §4), and it
  is supplied here.
* `lattice_fields` — all seven `q`/`W`/`A₀` fields at once.
* `exists_rawData_normData`, `hole52`, `tailSide` — `RawData ∧ NormData` with no hypothesis, then
  report 56's HOLE 52 and `PaddedLawSetup.TailSide` itself.

The scale in HOLE 52 is brief 60's: `c = √(ParamsAdopted2.stepSizeAdopted2 (m+1))`.
-/

set_option linter.unusedSectionVars false

namespace Submission.L10.RawDataInst2

open MeasureTheory Finset
open scoped RealInnerProductSpace
open Submission.L10 Submission.L10.Section5 Submission.L10.Tiling
open Submission.L10.ConstructionA Submission.L10.PaddedLawSetup
open Submission.L10.Increments Submission.L10.ChainWiring Submission.L10.TailSideSetup2
open Submission.L10.RawDataInst

variable {n : ℕ}

/-! ### 4. The chain's own `q`, `A₀`, and `NormData` -/

/-- The identity matrix in Frobenius coordinates. -/
noncomputable def idUT (n : ℕ) : EuclideanSpace ℝ (UT n) :=
  WithLp.toLp 2 fun p => if p.1.1 = p.1.2 then 1 else 0

@[simp] theorem idUT_apply (p : UT n) :
    (idUT n) p = if p.1.1 = p.1.2 then 1 else 0 := rfl

theorem up_fst_eq_snd_iff (i j : Fin n) : (up i j).1.1 = (up i j).1.2 ↔ i = j := by
  rcases le_total i j with h | h
  · rw [up_of_le h]
  · rw [up_comm, up_of_le h]; exact eq_comm

theorem symMat_idUT (n : ℕ) : symMat (idUT n) = (1 : Matrix (Fin n) (Fin n) ℝ) := by
  ext i j
  rw [symMat_apply, idUT_apply, Matrix.one_apply]
  by_cases h : i = j
  · rw [ite_eq_left ((up_fst_eq_snd_iff i j).2 h), ite_eq_left h, mul_one, cc_diag ((up_fst_eq_snd_iff i j).2 h)]
  · rw [ite_eq_right (fun hc => h ((up_fst_eq_snd_iff i j).1 hc)), ite_eq_right h, mul_zero]

/-- `⟪Id, q x⟫ = |x|²`. -/
theorem inner_idUT (x : Fin n → ℝ) : ⟪idUT n, qUT x⟫ = x ⬝ᵥ x := by
  rw [inner_qUT_eq_quad, symMat_idUT, Matrix.one_mulVec]

/-- The chain's initial state, Klartag's `a₀·Id` (eq. 61). -/
noncomputable def A0C (n : ℕ) : EuclideanSpace ℝ (UT n) := a0C n • idUT n

/-- The scaled lattice point, as a plain coordinate vector. -/
noncomputable def xOf (α : ℝ) {n : ℕ} (y : Fin n → ℤ) : Fin n → ℝ := fun i => α * (y i : ℝ)

theorem dotProduct_xOf (α : ℝ) {n : ℕ} (y : Fin n → ℤ) :
    xOf α y ⬝ᵥ xOf α y = (α * ‖toE n y‖) ^ 2 := by
  have hnorm : ‖toE n y‖ ^ 2 = ∑ i : Fin n, ((y i : ℝ)) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    exact Finset.sum_congr rfl (fun i _ => by rw [Tiling.toE_apply, Real.norm_eq_abs, sq_abs])
  rw [dotProduct, mul_pow, hnorm, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by rw [xOf]; ring)

/-- The chain's constraint vector at the scaled lattice point. -/
noncomputable def qC (α : ℝ) {n : ℕ} (y : Fin n → ℤ) : EuclideanSpace ℝ (UT n) := qUT (xOf α y)

theorem norm_qC (α : ℝ) {n : ℕ} (y : Fin n → ℤ) : ‖qC α y‖ = (α * ‖toE n y‖) ^ 2 := by
  have h : ‖qC α y‖ ^ 2 = ((α * ‖toE n y‖) ^ 2) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, qC, inner_qUT, dotProduct_xOf]
  have h2 : (0 : ℝ) ≤ (α * ‖toE n y‖) ^ 2 := sq_nonneg _
  nlinarith [norm_nonneg (qC α y), h, h2]

theorem inner_A0C_qC (α : ℝ) {n : ℕ} (y : Fin n → ℤ) :
    ⟪A0C n, qC α y⟫ = a0C n * (α * ‖toE n y‖) ^ 2 := by
  rw [A0C, qC, real_inner_smul_left, inner_idUT, dotProduct_xOf]

/-- **`NormData` for the chain's own data** — both fields, for any `W`. -/
theorem normData_qC (α : ℝ) {n : ℕ} (W : Finset (Fin n → ℤ)) :
    NormData n α (qC α) W (A0C n) :=
  ⟨fun y _ => norm_qC α y, fun y _ => inner_A0C_qC α y⟩

/-! ### 5. The window, and the seven lattice fields -/

open Classical in
/-- **The chain's window**: the integer points of the shell, between Klartag's inner radius
`(1−1/n)/α` (exclusive — this is where `hA₀` and `hy` come from) and `windowC α n − √n/2`
(inclusive — this is `hwin`). -/
noncomputable def shell (α : ℝ) (n : ℕ) : Finset (Fin n → ℤ) :=
  ((Tiling.finite_ball_integer n (windowC α n - Real.sqrt n / 2)).toFinset).filter
    (fun y => (1 - 1 / (n : ℝ)) / α < ‖toE n y‖)

open Classical in
theorem mem_shell {α : ℝ} {n : ℕ} {y : Fin n → ℤ} :
    y ∈ shell α n ↔
      ‖toE n y‖ ≤ windowC α n - Real.sqrt n / 2 ∧ (1 - 1 / (n : ℝ)) / α < ‖toE n y‖ := by
  rw [shell, Finset.mem_filter, Set.Finite.mem_toFinset]
  exact Iff.rfl

/-- The inner radius, unscaled: `α·‖toE y‖ > 1 − 1/n` on the shell. -/
theorem inner_radius {α : ℝ} (hα : 0 < α) {n : ℕ} {y : Fin n → ℤ} (hy : y ∈ shell α n) :
    1 - 1 / (n : ℝ) < α * ‖toE n y‖ := by
  have h := (mem_shell.1 hy).2
  rw [div_lt_iff₀ hα] at h
  linarith [h]

/-- `a₀·(α‖toE y‖)² > 1` on the shell — Klartag's eq. (61), and the source of both `hA₀`
and `hy`. -/
theorem a0C_mul_sq_gt_one {α : ℝ} (hα : 0 < α) {n : ℕ} (hn : 2 ≤ n) {y : Fin n → ℤ}
    (hy : y ∈ shell α n) : 1 < a0C n * (α * ‖toE n y‖) ^ 2 := by
  have hnr : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hb : (0 : ℝ) < 1 - 1 / (n : ℝ) := by
    have : 1 / (n : ℝ) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le (by norm_num) hnr
    linarith
  have hr := inner_radius hα hy
  have hsq : (1 - 1 / (n : ℝ)) ^ 2 < (α * ‖toE n y‖) ^ 2 := by nlinarith
  have hbb : (0 : ℝ) < (1 - 1 / (n : ℝ)) ^ 2 := by positivity
  rw [a0C, inv_pow, inv_mul_eq_div, lt_div_iff₀ hbb, one_mul]
  exact hsq

/-- **The seven lattice fields**, for the chain's own `q`, `A₀` and the shell. -/
theorem lattice_fields {α : ℝ} (hα : 0 < α) {n : ℕ} (hn : 3 ≤ n) :
    (∀ j : (Fin n → ℤ), ∀ i ∈ shell α n, (0 : ℝ) ≤ ⟪qC α i, qC α j⟫) ∧
    (∀ y ∈ shell α n, (1 : ℝ) < ⟪A0C n, qC α y⟫) ∧
    (∀ y ∈ shell α n, y ≠ 0) ∧
    (∀ y ∈ shell α n, ‖toE n y‖ ≤ windowC α n) ∧
    (∀ y ∈ shell α n, ‖toE n y‖ + Real.sqrt n / 2 ≤ windowC α n) ∧
    (∀ y ∈ shell α n, 0 < α * ‖toE n y‖) ∧
    (∀ k, k < ParamsAdopted2.numStepsAdopted2 n → k ≠ 0 → ∀ y ∈ shell α n,
      0 < yOf (a0C n) ((k : ℝ) * ParamsAdopted2.stepSizeAdopted2 n) (α * ‖toE n y‖)) := by
  have hn2 : 2 ≤ n := by omega
  have hnr : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hb : (0 : ℝ) < 1 - 1 / (n : ℝ) := by
    have : 1 / (n : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hnr
    linarith
  have hsqn : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hpos : ∀ y ∈ shell α n, 0 < α * ‖toE n y‖ := fun y hy =>
    lt_trans hb (inner_radius hα hy)
  refine ⟨fun j i _ => inner_qUT_nonneg _ _, fun y hy => ?_, fun y hy => ?_,
    fun y hy => ?_, fun y hy => ?_, hpos, ?_⟩
  · rw [inner_A0C_qC]; exact a0C_mul_sq_gt_one hα hn2 hy
  · intro hzero
    have h0 : (0 : ℝ) < α * ‖toE n y‖ := hpos y hy
    have hz : ‖toE n y‖ = 0 := by
      rw [hzero, EuclideanSpace.norm_eq]
      simp [Tiling.toE_apply]
    rw [hz, mul_zero] at h0
    exact lt_irrefl 0 h0
  · have := (mem_shell.1 hy).1
    linarith
  · have := (mem_shell.1 hy).1
    linarith
  · intro k hk hk0 y hy
    have ht : 0 < (k : ℝ) * ParamsAdopted2.stepSizeAdopted2 n := by
      have h1 : (0 : ℝ) < (k : ℝ) := by
        have : 0 < k := Nat.pos_of_ne_zero hk0
        exact_mod_cast this
      exact mul_pos h1 (TailSideSetup2.stepSizeAdopted2_pos hn)
    have hr0 : 0 < α * ‖toE n y‖ := hpos y hy
    have hgt := a0C_mul_sq_gt_one hα hn2 hy
    rw [yOf, div_pos_iff]
    left
    refine ⟨?_, Real.sqrt_pos.2 ht⟩
    rw [sub_pos, inv_lt_iff_one_lt_mul₀ (by positivity)]
    linarith [hgt]

/-! ### 6. `RawData ∧ NormData` with no hypothesis, HOLE 52, and `TailSide` -/

/-- **`rawData_exists`, unconditional**: `RawData` *and* `NormData`, for the chain's own `q`,
`A₀` and window. -/
theorem exists_rawData_normData (hn : 3 ≤ n) :
    ∃ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p) (α R : ℝ)
      (q : (Fin n → ℤ) → EuclideanSpace ℝ (UT n)) (W : Finset (Fin n → ℤ))
      (A₀ : EuclideanSpace ℝ (UT n)),
      RawData p n α R q W A₀ ∧ NormData n α q W A₀ := by
  obtain ⟨p, hp, α, hαpos, hαnorm, hαsmall, hM⟩ :=
    exists_prime_alpha_mul (by omega : 2 ≤ n) (max (2 * winNum n) (max 1 (Real.sqrt n)))
      (le_trans (le_max_left _ _) (le_max_right _ _))
  obtain ⟨hq, hA₀, hne0, hrad, hwin, hr, hy⟩ := lattice_fields hαpos hn
  exact ⟨p, ⟨hp⟩, ⟨hp.ne_zero⟩, α, (1 - 1 / (n : ℝ)) / α, qC α, shell α n, A0C n,
    rawData_of_lattice (by omega) hαpos hp.two_le hαnorm hαsmall hM hq hA₀ hne0 hrad hwin hr hy,
    normData_qC α (shell α n)⟩

/-- **HOLE 52 of report 56, with no hypothesis left.**  The scale is brief 60's
`√(stepSizeAdopted2 (m+1))`. -/
theorem hole52 :
    ∀ m : ℕ, Threshold2.n₁ ≤ m →
      ∃ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p) (c α R : ℝ)
        (q : (Fin (m + 1) → ℤ) → EuclideanSpace ℝ (UT (m + 1)))
        (W : Finset (Fin (m + 1) → ℤ)) (A₀ : EuclideanSpace ℝ (UT (m + 1))),
        3 ≤ m + 1 ∧ RawData p (m + 1) α R q W A₀ ∧ TailSideHyp (m + 1) c α q W A₀ := by
  intro m hm
  have h3 : 3 ≤ m + 1 := by
    have : 2073600 ≤ m := by simpa [Threshold2.n₁] using hm
    omega
  obtain ⟨p, hp, hp0, α, R, q, W, A₀, hraw, hnd⟩ := exists_rawData_normData h3
  exact ⟨p, hp, hp0, Real.sqrt (ParamsAdopted2.stepSizeAdopted2 (m + 1)), α, R, q, W, A₀,
    h3, hraw, TailSideSetup2.tailSideHyp_of_rawData hraw hnd h3⟩

/-- **`PaddedLawSetup.TailSide`** — report 56's hole (i), closed. -/
theorem tailSide : PaddedLawSetup.TailSide := PaddedLawSetup.tailSide_on_setup hole52

end Submission.L10.RawDataInst2

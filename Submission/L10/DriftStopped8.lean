import Submission.L10.DriftStopped7
import Submission.L10.Theorem4

/-!
# Gate L-10 (`klartag_packing`) — the lattice avoidance, modulo the far band

Brief 69.  **Name (rule 5).** The brief says to deliver into `DriftStopped7.lean`; that file was
reported in report 62b and is frozen, so this is a new module importing it.

Report 62 §3 named `chainOutput_of_logDet` as the gate's last theorem and its avoidance conjunct as
the hard part.  The avoidance splits by `‖toE y‖` into three bands and **two of the three are free**:

* **short**, `‖toE y‖ ≤ R`: the R-condition already says `y ∉ latZ p (m+1) g`.
* **shell**, `R < ‖toE y‖` and `‖toE y‖ + √(m+1)/2 ≤ windowC α (m+1)`: coverage puts `y` in the
  shell, so `y ∈ W_g`, and **`Chain.chain_fst_mem_kSet` gives `1 ≤ ⟪A_k, qC α y⟫` for every `k` and
  every `ω`** — the chain never leaves `K_L`, by construction of the lift.  With
  `ChainWiring.inner_qUT_eq_quad` that is `(symMat A *ᵥ x) ⬝ᵥ x ≥ 1`, i.e. `x ∉ ellipsoid`.
  *No contact hypothesis is needed*: the brief's `hnocontact` asks for more than the argument uses,
  and `countGood` bounds a count, not an occupancy.
* **far**, `windowC α (m+1) − √(m+1)/2 < ‖toE y‖`: `norm_lt_reach` says every point of
  `ellipsoid A` has `‖v‖ < 1/√m` when `StateBounds A m M` holds, so a lattice point at or beyond the
  **reach** is out for free.  What is left is the band between the window and the reach — scaled,
  `(1.000053, 1.0336]` — where the tree counts nothing.  That is `BandHyp`, the one hypothesis.

`chainOutput_of_state` assembles `Assembly.ChainOutput α g (exp (−C'/2))`, so **`c₀`'s value is
produced here**: report 56 item (iii) recorded that `c₀` is given a value nowhere in the tree.

`driftSide'''_of_stateSupply` reduces `Theorem4.DriftSide'''` to `StateSupply`: the probabilistic
half must hand over a chain state in `K_L` with `StateBounds` and the eq. (68) log-determinant
bound.  `driftSide'''_of_obligation_of_band` is the same with the band hoisted out and the state
supply taken at the adopted lower bound.
-/

set_option linter.unusedSectionVars false

namespace Submission.L10.DriftStopped8

open MeasureTheory Matrix Finset Module Submission.L10 Submission.L10.Increments
open Submission.L10.ConstructionA Submission.L10.Tiling Submission.L10.PaddedLawSetup
open Submission.L10.TailSideSetup2 Submission.L10.RawDataInst2 Submission.L10.Theorem2
open Submission.L10.DriftStopped7
open scoped ENNReal RealInnerProductSpace

/-! ## 1. The reach of the ellipsoid -/

section Reach

variable {N : ℕ}

/-- The ellipsoid's quadratic form as an inner product, so `StateBounds.lower` applies to it. -/
theorem quad_eq_inner (A : Matrix (Fin N) (Fin N) ℝ) (v : EuclideanSpace ℝ (Fin N)) :
    (A *ᵥ v.ofLp) ⬝ᵥ v.ofLp = ⟪v, Matrix.toEuclideanCLM (𝕜 := ℝ) A v⟫ := by
  rw [Matrix.inner_toEuclideanCLM]
  exact dotProduct_comm _ _

/-- **The reach.**  `StateBounds A m M` bounds the ellipsoid inside the ball of radius `1/√m`:
`m‖v‖² ≤ ⟪v, Av⟫ < 1`. -/
theorem norm_lt_reach {A : Matrix (Fin N) (Fin N) ℝ} {mLow M : ℝ}
    (hSB : Discharge.StateBounds A mLow M) {v : EuclideanSpace ℝ (Fin N)}
    (hv : v ∈ ChainEllipsoid.ellipsoid A) : ‖v‖ < 1 / Real.sqrt mLow := by
  have hm : 0 < mLow := hSB.mpos
  have hs : 0 < Real.sqrt mLow := Real.sqrt_pos.2 hm
  have hsq : Real.sqrt mLow ^ 2 = mLow := Real.sq_sqrt hm.le
  have hq : (A *ᵥ v.ofLp) ⬝ᵥ v.ofLp < 1 := hv
  rw [quad_eq_inner] at hq
  have h1 : mLow * ‖v‖ ^ 2 < 1 := lt_of_le_of_lt (hSB.lower v) hq
  by_contra hcon
  have hge : 1 / Real.sqrt mLow ≤ ‖v‖ := not_lt.1 hcon
  have hpos : 0 < 1 / Real.sqrt mLow := by positivity
  have hsq2 : (1 / Real.sqrt mLow) ^ 2 ≤ ‖v‖ ^ 2 := by nlinarith [hge, hpos]
  have hval : (1 / Real.sqrt mLow) ^ 2 = 1 / mLow := by rw [div_pow, one_pow, hsq]
  rw [hval] at hsq2
  have hfin : 1 ≤ ‖v‖ ^ 2 * mLow := (div_le_iff₀ hm).1 hsq2
  nlinarith [hfin, h1]

/-- A lattice point at or beyond the reach is outside the ellipsoid, with no counting at all. -/
theorem notMem_ellipsoid_of_reach {A : Matrix (Fin N) (Fin N) ℝ} {mLow M : ℝ}
    (hSB : Discharge.StateBounds A mLow M) {v : EuclideanSpace ℝ (Fin N)}
    (hv : 1 / Real.sqrt mLow ≤ ‖v‖) : v ∉ ChainEllipsoid.ellipsoid A :=
  fun hmem => absurd (norm_lt_reach hSB hmem) (not_lt.2 hv)

end Reach

/-! ## 2. The shell case: `K_L` membership is the avoidance -/

section Shell

variable {n : ℕ}

theorem toLp_xOf_eq (α : ℝ) (y : Fin n → ℤ) :
    (WithLp.toLp 2 (xOf α y) : EuclideanSpace ℝ (Fin n)) = α • toE n y := rfl

theorem norm_toLp_xOf {α : ℝ} (hα : 0 ≤ α) (y : Fin n → ℤ) :
    ‖(WithLp.toLp 2 (xOf α y) : EuclideanSpace ℝ (Fin n))‖ = α * ‖toE n y‖ := by
  rw [toLp_xOf_eq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hα]

/-- **The shell case, and it needs no probabilistic input.**  `Chain.kSet` is the set of matrices
whose ellipsoid misses the window, and `Chain.chain_fst_mem_kSet` keeps the chain inside it at every
step and on every path. -/
theorem notMem_ellipsoid_of_mem_kSet {α : ℝ} {W : Finset (Fin n → ℤ)}
    {A : EuclideanSpace ℝ (UT n)} (hA : A ∈ Chain.kSet (qC α) W) {y : Fin n → ℤ} (hy : y ∈ W) :
    (WithLp.toLp 2 (xOf α y) : EuclideanSpace ℝ (Fin n))
      ∉ ChainEllipsoid.ellipsoid (symMat A) := by
  intro hmem
  have h1 : (1 : ℝ) ≤ ⟪A, qC α y⟫ := hA y hy
  have h2 : ⟪A, qC α y⟫ = (symMat A *ᵥ xOf α y) ⬝ᵥ xOf α y :=
    ChainWiring.inner_qUT_eq_quad A (xOf α y)
  have h3 : (symMat A *ᵥ xOf α y) ⬝ᵥ xOf α y < 1 := hmem
  rw [h2] at h1
  linarith

end Shell

/-! ## 3. The band -/

/-- **The one hypothesis.**  Every point of `Λ(g)` beyond the window is at or beyond the ellipsoid's
reach `1/√mLow` — i.e. the band `(windowC α n − √n/2, 1/(α√mLow))` holds no lattice point.  The
window is `1.000053` and the reach `1.0336` at the adopted parameters, so this is a genuine gap and
brief 68 is pricing its repair. -/
def BandHyp (p m : ℕ) (α mLow : ℝ) (g : Fin (m + 1) → ZMod p) : Prop :=
  ∀ y : Fin (m + 1) → ℤ, y ≠ 0 → y ∈ latZ p (m + 1) g →
    windowC α (m + 1) - Real.sqrt ((m + 1 : ℕ) : ℝ) / 2 < ‖toE (m + 1) y‖ →
    1 / Real.sqrt mLow ≤ α * ‖toE (m + 1) y‖

/-! ## 4. The three cases, and `ChainOutput` -/

section Assembly

variable {m p : ℕ}

/-- **The avoidance, by the three bands.**  Short: the R-condition.  Shell: `K_L`.  Far: the reach,
past the band. -/
theorem avoid_of_cases {α : ℝ} (hα : 0 < α) {g : Fin (m + 1) → ZMod p}
    {A : EuclideanSpace ℝ (UT (m + 1))} {mLow M : ℝ}
    (hSB : Discharge.StateBounds (symMat A) mLow M)
    (hkSet : A ∈ Chain.kSet (qC α) (windowOf α p m g))
    (hcov : ∀ y : Fin (m + 1) → ℤ, y ≠ 0 →
      (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α < ‖toE (m + 1) y‖ →
      ‖toE (m + 1) y‖ + Real.sqrt ((m + 1 : ℕ) : ℝ) / 2 ≤ windowC α (m + 1) →
        y ∈ shell α (m + 1))
    (hfree : ∀ y : Fin (m + 1) → ℤ, y ≠ 0 →
      ‖toE (m + 1) y‖ ≤ (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α → y ∉ latZ p (m + 1) g)
    (hband : BandHyp p m α mLow g) :
    ∀ y : Fin (m + 1) → ℤ, y ≠ 0 → y ∈ latZ p (m + 1) g →
      (WithLp.toLp 2 (xOf α y) : EuclideanSpace ℝ (Fin (m + 1)))
        ∉ ChainEllipsoid.ellipsoid (symMat A) := by
  intro y hy0 hylat
  by_cases hshort : ‖toE (m + 1) y‖ ≤ (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α
  · exact absurd hylat (hfree y hy0 hshort)
  have hlong : (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α < ‖toE (m + 1) y‖ := not_le.1 hshort
  by_cases hin : ‖toE (m + 1) y‖ + Real.sqrt ((m + 1 : ℕ) : ℝ) / 2 ≤ windowC α (m + 1)
  · exact notMem_ellipsoid_of_mem_kSet hkSet (mem_windowOf.2 ⟨hcov y hy0 hlong hin, hylat⟩)
  · have hfar : windowC α (m + 1) - Real.sqrt ((m + 1 : ℕ) : ℝ) / 2 < ‖toE (m + 1) y‖ := by
      have hgt := not_le.1 hin
      linarith
    have hreach := hband y hy0 hylat hfar
    rw [← norm_toLp_xOf hα.le y] at hreach
    exact notMem_ellipsoid_of_reach hSB hreach

/-- **`Assembly.ChainOutput` from a chain state.**  `StateBounds.congr` supplies the congruence,
`StateBounds.posDef` the determinant's sign, `Assembly.sqrt_det_le` eq. (68), and the avoidance is
`avoid_of_cases`.  **`c₀ = exp(−C'/2)`** — report 17 §2.3's value, produced here. -/
theorem chainOutput_of_state (hm0 : m ≠ 0) {α : ℝ} {g : Fin (m + 1) → ZMod p}
    {A : EuclideanSpace ℝ (UT (m + 1))} {mLow M C' : ℝ}
    (hSB : Discharge.StateBounds (symMat A) mLow M)
    (hlog : ChainWiring.logDet A ≤ C' - 4 * Real.log ((m + 1 : ℕ) : ℝ))
    (havoid : ∀ y : Fin (m + 1) → ℤ, y ≠ 0 → y ∈ latZ p (m + 1) g →
      (WithLp.toLp 2 (xOf α y) : EuclideanSpace ℝ (Fin (m + 1)))
        ∉ ChainEllipsoid.ellipsoid (symMat A)) :
    Assembly.ChainOutput α g (Real.exp (-C' / 2)) := by
  obtain ⟨S, hSherm, hSA⟩ := hSB.congr
  have hST : Sᵀ = S := GoodEvent.isSymm_of_isHermitian hSherm
  have hdet : 0 < (symMat A).det := hSB.posDef.det_pos
  have hmR : (0 : ℝ) < (m : ℝ) := by
    have : 0 < m := Nat.pos_of_ne_zero hm0
    exact_mod_cast this
  have hmono : Real.log ((m : ℝ)) ≤ Real.log (((m + 1 : ℕ) : ℝ)) := by
    refine Real.log_le_log hmR ?_
    exact_mod_cast Nat.le_succ m
  have hlog' : Real.log ((symMat A).det) ≤ C' - 4 * Real.log ((m : ℕ) : ℝ) := by
    rw [ChainWiring.logDet] at hlog
    linarith
  have hsd : Real.sqrt ((symMat A).det) ≤ Real.exp (C' / 2) / (m : ℝ) ^ 2 :=
    Assembly.sqrt_det_le hdet hm0 hlog'
  refine ⟨symMat A, S, hdet, by rw [hST]; exact hSA, ?_, ?_⟩
  · have hexp : Real.exp (C' / 2) * Real.exp (-C' / 2) = 1 := by
      rw [← Real.exp_add, show C' / 2 + -C' / 2 = 0 by ring, Real.exp_zero]
    have hnn : (0 : ℝ) ≤ Real.exp (-C' / 2) * (m : ℝ) ^ 2 := by positivity
    have hstep : Real.sqrt ((symMat A).det) * (Real.exp (-C' / 2) * (m : ℝ) ^ 2)
        ≤ (Real.exp (C' / 2) / (m : ℝ) ^ 2) * (Real.exp (-C' / 2) * (m : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hsd hnn
    have hval : (Real.exp (C' / 2) / (m : ℝ) ^ 2) * (Real.exp (-C' / 2) * (m : ℝ) ^ 2)
        = Real.exp (C' / 2) * Real.exp (-C' / 2) := by field_simp
    rw [hval, hexp] at hstep
    exact hstep
  · rintro x ⟨v, hv, rfl⟩ hx0
    obtain ⟨y, hy, rfl⟩ := hv
    have hxeq : α • (toReal (m + 1) y) = xOf α y := by
      funext i
      simp only [xOf, Pi.smul_apply, smul_eq_mul, toReal_apply]
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact hx0 (by simp)
    show (WithLp.toLp 2 (α • (toReal (m + 1) y)) : EuclideanSpace ℝ (Fin (m + 1)))
        ∉ ChainEllipsoid.ellipsoid (symMat A)
    rw [hxeq]
    exact havoid y hy0 hy

end Assembly

/-! ## 5. `Theorem4.DriftSide'''`, reduced to a state supply -/

section Side

/-- **What the probabilistic half must hand over.**  A chain state on the drift's own window
`W_g`, inside `K_L`, with `StateBounds` and the eq. (68) log-determinant bound — plus the band. -/
def StateSupply (C' : ℝ) : Prop :=
  ∀ m : ℕ, Threshold2.n₁ ≤ m → ∀ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p) (α : ℝ),
    0 < α → ∀ (hn : 3 ≤ m + 1)
      (hraw : RawData p (m + 1) α ((1 - 1 / ((m + 1 : ℕ) : ℝ)) / α)
        (qC α) (shell α (m + 1)) (A0C (m + 1)))
      (hnd : NormData (m + 1) α (qC α) (shell α (m + 1)) (A0C (m + 1))),
      (∀ y : Fin (m + 1) → ℤ, y ≠ 0 →
        (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α < ‖toE (m + 1) y‖ →
        ‖toE (m + 1) y‖ + Real.sqrt ((m + 1 : ℕ) : ℝ) / 2 ≤ windowC α (m + 1) →
          y ∈ shell α (m + 1)) →
      ∀ (g : Fin (m + 1) → ZMod p), g ≠ 0 →
      (∀ y : Fin (m + 1) → ℤ, y ≠ 0 →
        ‖toE (m + 1) y‖ ≤ (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α → y ∉ latZ p (m + 1) g) →
      LightContact (chainW hn hraw hnd) (shell α (m + 1))
        (ENNReal.ofReal (64 * C1C α (m + 1))) g →
      ∃ (A : EuclideanSpace ℝ (UT (m + 1))) (mLow M : ℝ),
        A ∈ Chain.kSet (qC α) (windowOf α p m g) ∧
        Discharge.StateBounds (symMat A) mLow M ∧
        ChainWiring.logDet A ≤ C' - 4 * Real.log ((m + 1 : ℕ) : ℝ) ∧
        BandHyp p m α mLow g

/-- **The drift side from the state supply.**  `c₀ = exp(−C'/2)`, produced, not assumed. -/
theorem driftSide'''_of_stateSupply {C' : ℝ} (h : StateSupply C') :
    Theorem4.DriftSide''' (Real.exp (-C' / 2)) := by
  intro m hm p hp hp0 α hα hn hraw hnd hcov g hg hfree hlight
  obtain ⟨A, mLow, M, hkSet, hSB, hlog, hband⟩ :=
    h m hm p hp hp0 α hα hn hraw hnd hcov g hg hfree hlight
  have hm0 : m ≠ 0 := by
    have h2 : 2073600 ≤ m := by simpa [Threshold2.n₁] using hm
    omega
  exact chainOutput_of_state hm0 hSB hlog
    (avoid_of_cases hα hSB hkSet hcov hfree hband)

/-- **The challenge statement from the state supply alone.** -/
theorem klartag_packing_of_stateSupply {C' : ℝ} (h : StateSupply C') :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      let V := EuclideanSpace ℝ (Fin (n + 1))
      ∃ φ : V →ₗ[ℝ] V, let E := φ '' Metric.ball (0 : V) 1
        (MeasureTheory.volume E : EReal) = c * n ^ 2 ∧
        {v ∈ E | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} :=
  Theorem4.klartag_packing_of_driftSide'''
    ⟨Real.exp (-C' / 2), Real.exp_pos _, driftSide'''_of_stateSupply h⟩

end Side

/-! ## 6. The band hoisted out, at the adopted lower bound -/

section Adopted

/-- The band, at the state lower bound `DriftStopped6.mAdopted`, for every dimension and line. -/
def BandSideAdopted : Prop :=
  ∀ m : ℕ, Threshold2.n₁ ≤ m → ∀ (p : ℕ) (α : ℝ) (g : Fin (m + 1) → ZMod p),
    BandHyp p m α (DriftStopped6.mAdopted (m + 1)) g

/-- The state supply with `mLow` fixed at the adopted lower bound and the band removed. -/
def StateSupplyAdopted (C' : ℝ) : Prop :=
  ∀ m : ℕ, Threshold2.n₁ ≤ m → ∀ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p) (α : ℝ),
    0 < α → ∀ (hn : 3 ≤ m + 1)
      (hraw : RawData p (m + 1) α ((1 - 1 / ((m + 1 : ℕ) : ℝ)) / α)
        (qC α) (shell α (m + 1)) (A0C (m + 1)))
      (hnd : NormData (m + 1) α (qC α) (shell α (m + 1)) (A0C (m + 1))),
      (∀ y : Fin (m + 1) → ℤ, y ≠ 0 →
        (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α < ‖toE (m + 1) y‖ →
        ‖toE (m + 1) y‖ + Real.sqrt ((m + 1 : ℕ) : ℝ) / 2 ≤ windowC α (m + 1) →
          y ∈ shell α (m + 1)) →
      ∀ (g : Fin (m + 1) → ZMod p), g ≠ 0 →
      (∀ y : Fin (m + 1) → ℤ, y ≠ 0 →
        ‖toE (m + 1) y‖ ≤ (1 - 1 / ((m + 1 : ℕ) : ℝ)) / α → y ∉ latZ p (m + 1) g) →
      LightContact (chainW hn hraw hnd) (shell α (m + 1))
        (ENNReal.ofReal (64 * C1C α (m + 1))) g →
      ∃ (A : EuclideanSpace ℝ (UT (m + 1))) (M : ℝ),
        A ∈ Chain.kSet (qC α) (windowOf α p m g) ∧
        Discharge.StateBounds (symMat A) (DriftStopped6.mAdopted (m + 1)) M ∧
        ChainWiring.logDet A ≤ C' - 4 * Real.log ((m + 1 : ℕ) : ℝ)

/-- **Goal (5): the drift side with the band as the one extra hypothesis.** -/
theorem driftSide'''_of_obligation_of_band {C' : ℝ} (hband : BandSideAdopted)
    (h : StateSupplyAdopted C') : ∃ c₀ : ℝ, 0 < c₀ ∧ Theorem4.DriftSide''' c₀ := by
  refine ⟨Real.exp (-C' / 2), Real.exp_pos _, driftSide'''_of_stateSupply ?_⟩
  intro m hm p hp hp0 α hα hn hraw hnd hcov g hg hfree hlight
  obtain ⟨A, M, hkSet, hSB, hlog⟩ := h m hm p hp hp0 α hα hn hraw hnd hcov g hg hfree hlight
  exact ⟨A, DriftStopped6.mAdopted (m + 1), M, hkSet, hSB, hlog, hband m hm p α g⟩

end Adopted

end Submission.L10.DriftStopped8

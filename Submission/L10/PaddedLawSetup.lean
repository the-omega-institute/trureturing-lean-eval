import Submission.L10.ChainSetup

/-!
# Gate L-10 (`klartag_packing`), brief 50 — the padded increment law on `chainSetup`

## How the fresh coordinates enter, exactly

Report 47 said the padding's fresh coordinates come from changing the **value type** `F` rather
than adding a factor.  This module makes that precise and proves it:

`F := PadCarrier n = WithLp 2 (EuclideanSpace ℝ (UT n) × ℝ)`,

and `stdGaussian_prodL2` says the standard Gaussian on that carrier **is** the product of the
standard Gaussian on the chain's carrier with `N(0,1)` on the fresh line:

`((stdGaussian E).prod (stdGaussian ℝ)).map (WithLp.toLp 2) = stdGaussian (WithLp 2 (E × ℝ))`.

So on `gaussPath (PadCarrier n)` the chain's increment is `coordFst k` and the fresh coordinate is
`coordSnd k`; `map_coordFst` and `map_coordSnd` are their laws and `indepFun_coordFst_coordSnd`
their independence — at each step, and across steps by `iIndepFun_coord`.  That is the whole of
"the fresh coordinates enter through `F`", and none of it needs a second factor.

## What is proved here

* `stdGaussian_prodL2`, `map_fst_stdGaussian`, `map_snd_stdGaussian` — the value-type fact.
* `padded_law_on_setup` at **every** horizon `N`, in the exact shape `hprop_of_hincl` consumes, and
  `tail_on_setup`, both at the two-factor carrier (they are `ChainSetup`'s, which is reported and
  frozen, restated here at `PadCarrier` so that the brief's names exist at the carrier in use).
* `padWalk_eq_of_dir`, which identifies the padded walk's increments with the chain's martingale
  increment plus the fresh coordinate read in the completed unit direction.

`chainRaw2_on_setup` is **not** here; §4 of the report says exactly what separates it.
-/

set_option linter.unusedSectionVars false

namespace Submission.L10.PaddedLawSetup

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal RealInnerProductSpace
open Submission.L10 Submission.L10.Increments Submission.L10.ChainSetup
open Submission.L10.Tiling Submission.L10.Section5 Submission.L10.ConstructionA

noncomputable section

/-! ## 1. The value-type fact -/

section ValueType

variable (E G : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasurableSpace G] [BorelSpace G]

theorem norm_sq_toLp (x : E) (y : G) :
    ‖(WithLp.toLp 2 (x, y) : WithLp 2 (E × G))‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2]; simp

theorem norm_toLp_left (x : E) : ‖(WithLp.toLp 2 (x, (0 : G)) : WithLp 2 (E × G))‖ = ‖x‖ := by
  have h : ‖(WithLp.toLp 2 (x, (0 : G)) : WithLp 2 (E × G))‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [norm_sq_toLp]; simp
  nlinarith [norm_nonneg (WithLp.toLp 2 (x, (0 : G)) : WithLp 2 (E × G)), norm_nonneg x]

theorem norm_toLp_right (y : G) : ‖(WithLp.toLp 2 ((0 : E), y) : WithLp 2 (E × G))‖ = ‖y‖ := by
  have h : ‖(WithLp.toLp 2 ((0 : E), y) : WithLp 2 (E × G))‖ ^ 2 = ‖y‖ ^ 2 := by
    rw [norm_sq_toLp]; simp
  nlinarith [norm_nonneg (WithLp.toLp 2 ((0 : E), y) : WithLp 2 (E × G)), norm_nonneg y]

/-- **The first summand of a standard Gaussian is a standard Gaussian.** -/
theorem map_fst_stdGaussian :
    (stdGaussian (WithLp 2 (E × G))).map (fun x => (WithLp.ofLp x).1) = stdGaussian E := by
  refine Measure.ext_of_charFun ?_
  funext t
  rw [Increments.charFun_map_of_inner (stdGaussian (WithLp 2 (E × G)))
      (fun x => (WithLp.ofLp x).1) (by fun_prop)
      (fun s : E => (WithLp.toLp 2 (s, (0 : G)) : WithLp 2 (E × G)))
      (fun x s => by simp [WithLp.prod_inner_apply]),
    charFun_stdGaussian, charFun_stdGaussian, norm_toLp_left]

/-- **…and so is the second.**  This is the fresh coordinate. -/
theorem map_snd_stdGaussian :
    (stdGaussian (WithLp 2 (E × G))).map (fun x => (WithLp.ofLp x).2) = stdGaussian G := by
  refine Measure.ext_of_charFun ?_
  funext t
  rw [Increments.charFun_map_of_inner (stdGaussian (WithLp 2 (E × G)))
      (fun x => (WithLp.ofLp x).2) (by fun_prop)
      (fun s : G => (WithLp.toLp 2 ((0 : E), s) : WithLp 2 (E × G)))
      (fun x s => by simp [WithLp.prod_inner_apply]),
    charFun_stdGaussian, charFun_stdGaussian, norm_toLp_right]

/-- **The value-type fact.**  The standard Gaussian on the `L²` product *is* the product of the two
standard Gaussians — so adjoining the fresh coordinate to the value type is exactly adjoining an
independent `N(0,1)`, with no second factor and no reshuffling. -/
theorem stdGaussian_prodL2 :
    ((stdGaussian E).prod (stdGaussian G)).map (WithLp.toLp 2)
      = stdGaussian (WithLp 2 (E × G)) := by
  refine Measure.ext_of_charFun ?_
  funext t
  have hmeas : Measurable (WithLp.toLp 2 : E × G → WithLp 2 (E × G)) :=
    WithLp.measurable_toLp _ _
  have hcont : Continuous fun y : WithLp 2 (E × G) =>
      Complex.exp ((⟪y, t⟫ : ℝ) * Complex.I) := by
    refine Complex.continuous_exp.comp (Continuous.mul ?_ continuous_const)
    exact Complex.continuous_ofReal.comp
      (continuous_inner.comp (continuous_id.prodMk continuous_const))
  rw [charFun_apply, integral_map hmeas.aemeasurable hcont.aestronglyMeasurable]
  have hsplit : ∀ p : E × G,
      Complex.exp ((⟪(WithLp.toLp 2 p : WithLp 2 (E × G)), t⟫ : ℝ) * Complex.I)
        = Complex.exp ((⟪p.1, (WithLp.ofLp t).1⟫ : ℝ) * Complex.I)
          * Complex.exp ((⟪p.2, (WithLp.ofLp t).2⟫ : ℝ) * Complex.I) := by
    intro p
    rw [← Complex.exp_add]
    congr 1
    have h : (⟪(WithLp.toLp 2 p : WithLp 2 (E × G)), t⟫ : ℝ)
        = ⟪p.1, (WithLp.ofLp t).1⟫ + ⟪p.2, (WithLp.ofLp t).2⟫ := by
      simp [WithLp.prod_inner_apply]
    rw [h]
    push_cast
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hsplit)]
  rw [integral_prod_mul (μ := stdGaussian E) (ν := stdGaussian G)
      (fun x : E => Complex.exp ((⟪x, (WithLp.ofLp t).1⟫ : ℝ) * Complex.I))
      (fun y : G => Complex.exp ((⟪y, (WithLp.ofLp t).2⟫ : ℝ) * Complex.I)),
    ← charFun_apply, ← charFun_apply, charFun_stdGaussian, charFun_stdGaussian,
    charFun_stdGaussian, ← Complex.exp_add]
  congr 1
  have hn : ‖t‖ ^ 2 = ‖(WithLp.ofLp t).1‖ ^ 2 + ‖(WithLp.ofLp t).2‖ ^ 2 :=
    WithLp.prod_norm_sq_eq_of_L2 t
  rw [show ((‖t‖ : ℝ) : ℂ) ^ 2 = ((‖t‖ ^ 2 : ℝ) : ℂ) by push_cast; ring, hn]
  push_cast
  ring

end ValueType

/-! ## 2. The chain increment and the fresh coordinate on `gaussPath (PadCarrier n)` -/

section Carrier

variable {n : ℕ}

/-- The chain's driving increment at step `k`: the first summand. -/
def coordFst (k : ℕ) (ω : ℕ → PadCarrier n) : EuclideanSpace ℝ (UT n) :=
  (WithLp.ofLp (coord k ω)).1

/-- The padding's fresh coordinate at step `k`: the second summand. -/
def coordSnd (k : ℕ) (ω : ℕ → PadCarrier n) : ℝ := (WithLp.ofLp (coord k ω)).2

theorem measurable_coordFst (k : ℕ) : Measurable (coordFst (n := n) k) :=
  ((WithLp.measurable_ofLp _ _).comp (measurable_coord k)).fst

theorem measurable_coordSnd (k : ℕ) : Measurable (coordSnd (n := n) k) :=
  ((WithLp.measurable_ofLp _ _).comp (measurable_coord k)).snd

/-- **The chain's increment is a standard Gaussian on the chain's carrier.** -/
theorem map_coordFst (k : ℕ) :
    (gaussPath (PadCarrier n)).map (coordFst k) = stdGaussian (EuclideanSpace ℝ (UT n)) := by
  rw [show (coordFst (n := n) k) = (fun x : PadCarrier n => (WithLp.ofLp x).1) ∘ coord k from rfl,
    ← Measure.map_map (by fun_prop) (measurable_coord k), map_coord k, map_fst_stdGaussian]

/-- **The fresh coordinate is `N(0,1)`, independent of it.** -/
theorem map_coordSnd (k : ℕ) :
    (gaussPath (PadCarrier n)).map (coordSnd k) = stdGaussian ℝ := by
  rw [show (coordSnd (n := n) k) = (fun x : PadCarrier n => (WithLp.ofLp x).2) ∘ coord k from rfl,
    ← Measure.map_map (by fun_prop) (measurable_coord k), map_coord k, map_snd_stdGaussian]

end Carrier

/-! ### The bridge to the *external* padding factor -/

section External

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **The chain coordinate and an external fresh coordinate are one standard Gaussian.**  On
`gaussPath E ×ₘ (Fin N fresh Gaussians)` the pair `(ω.1 i, ω.2 ⟨i,_⟩)` has law
`stdGaussian (WithLp 2 (E × ℝ))` — `stdGaussian_prodL2` applied to the two factors' own laws.
This is the bridge `hprop` for the chain's `constraintM` needs, where the padding must live on
`hit_tail_yOf`'s external factor rather than inside the value type. -/
theorem map_pair_prod {N : ℕ} (i : ℕ) (hi : i < N) :
    ((gaussPath E).prod (Measure.pi fun _ : Fin N => stdGaussian ℝ)).map
        (fun ω : (ℕ → E) × (Fin N → ℝ) =>
          (WithLp.toLp 2 (ω.1 i, ω.2 ⟨i, hi⟩) : WithLp 2 (E × ℝ)))
      = stdGaussian (WithLp 2 (E × ℝ)) := by
  have hpair : (fun ω : (ℕ → E) × (Fin N → ℝ) => (ω.1 i, ω.2 ⟨i, hi⟩))
      = Prod.map (fun v : ℕ → E => v i) (fun v : Fin N → ℝ => v ⟨i, hi⟩) := rfl
  have hcomp : (fun ω : (ℕ → E) × (Fin N → ℝ) =>
        (WithLp.toLp 2 (ω.1 i, ω.2 ⟨i, hi⟩) : WithLp 2 (E × ℝ)))
      = (WithLp.toLp 2 : E × ℝ → WithLp 2 (E × ℝ))
        ∘ (fun ω : (ℕ → E) × (Fin N → ℝ) => (ω.1 i, ω.2 ⟨i, hi⟩)) := rfl
  have h1 : (gaussPath E).map (fun v : ℕ → E => v i) = stdGaussian E := map_coord i
  have h2 : (Measure.pi fun _ : Fin N => stdGaussian ℝ).map (fun v : Fin N → ℝ => v ⟨i, hi⟩)
      = stdGaussian ℝ := (measurePreserving_eval (fun _ : Fin N => stdGaussian ℝ) ⟨i, hi⟩).map_eq
  rw [hcomp, ← Measure.map_map (WithLp.measurable_toLp _ _) (by fun_prop), hpair,
    ← Measure.map_prod_map _ _ (measurable_pi_apply i) (measurable_pi_apply _),
    h1, h2, stdGaussian_prodL2]

end External

/-! ## 3. `padded_law_on_setup` at every horizon, and `tail_on_setup` -/

section Padded

variable {n : ℕ}

/-- **`hincl` at every horizon `N` on `chainSetup`**, in the exact shape
`WalkTelescope.hprop_of_hincl` consumes: the padded increment vector — the chain's martingale
increment plus the fresh coordinate read in the completed unit direction — is i.i.d. `N(0, r²)`. -/
theorem padded_law_on_setup {r : ℝ}
    {w : ℕ → (ℕ → PadCarrier n) → EuclideanSpace ℝ (UT n)}
    (hwm : ∀ k, Measurable (w k)) (hw1 : ∀ k p, ‖w k p‖ ≤ 1) (M₀ : ℝ) (N : ℕ) :
    ((gaussPath (PadCarrier n)).prod
        (Measure.pi fun _ : Fin N => gaussianReal 0 (Real.toNNReal (r ^ 2)))).map
        (padIncVec (padWalk r (padDir w) M₀) (fun _ _ => (0 : ℝ)) N)
      = Measure.pi fun _ : Fin N => gaussianReal 0 (Real.toNNReal (r ^ 2)) :=
  ChainSetup.padded_law_on_setup (padDir w) (measurable_padDir hwm) (norm_padDir_eq_one hw1) M₀ N

/-- **The transported per-step tail on `chainSetup`, with no hypothesis left.** -/
theorem tail_on_setup {r : ℝ} {w : ℕ → (ℕ → PadCarrier n) → EuclideanSpace ℝ (UT n)}
    (hwm : ∀ k, Measurable (w k)) (hw1 : ∀ k p, ‖w k p‖ ≤ 1)
    {N : ℕ} {a₀ u t : ℝ} (ht : 0 < t) (hM₀ : 0 < a₀ - (u ^ 2)⁻¹)
    (hv : ((N • Real.toNNReal (r ^ 2) : ℝ≥0) : ℝ) = t * 1 ^ 2) :
    (gaussPath (PadCarrier n))
        {ω | ∃ j ≤ N, padWalk r (padDir w) (a₀ - (u ^ 2)⁻¹) j ω ≤ 0}
      ≤ ENNReal.ofReal (4 * Phi (yOf a₀ t u)) :=
  ChainSetup.tail_on_padCarrier hwm hw1 ht hM₀ hv

/-- **The padded walk's increments, written out in the chain's own terms**: the martingale
increment `⟪ξ_k, w_k⟫` at scale `r`, plus the fresh coordinate `η_k` at the completing amplitude
`r√(1 − ‖w_k‖²)`.  This is the identity `chainRaw2_on_setup` has to match against
`ChainWalk.pureWalk_succ_sub`. -/
theorem padWalk_succ_sub {r : ℝ} (w : ℕ → (ℕ → PadCarrier n) → EuclideanSpace ℝ (UT n))
    (M₀ : ℝ) (k : ℕ) (ω : ℕ → PadCarrier n) :
    padWalk r (padDir w) M₀ (k + 1) ω - padWalk r (padDir w) M₀ k ω
      = -(r * (⟪coordFst k ω, w k (pastOf coord k ω)⟫
          + coordSnd k ω * Real.sqrt (1 - ‖w k (pastOf coord k ω)‖ ^ 2))) := by
  show (M₀ - ∑ i ∈ Finset.range (k + 1), padInc r (coord (F := PadCarrier n)) (padDir w) i ω)
      - (M₀ - ∑ i ∈ Finset.range k, padInc r (coord (F := PadCarrier n)) (padDir w) i ω) = _
  rw [Finset.sum_range_succ, padInc_padDir]
  simp only [coordFst, coordSnd]
  ring

end Padded

/-! ## 4. The composition: `ChainRaw2` on `chainSetup`, and the tail side of `ChainDelivers`

`ChainWalk.chainRaw2_of_walk` takes exactly one probabilistic argument, `hprop`.  On `chainSetup`
that argument is `TailSideHyp` below.  **It is not `tail_on_setup`**: `tail_on_setup` bounds the
hitting event of the *padded* walk, and `padWalk = constraintM − padSum` with `padSum` of both
signs, so neither event contains the other (report 50 §3).  `hit_tail_yOf`'s conclusion is about
`M` on `Ω₁` alone with the padding auxiliary on its external factor, which is the route
`map_pair_prod` opens.  Everything else in the composition is discharged here. -/

section Composition

/-- **The one probabilistic input of `chainRaw2_of_walk`, on `chainSetup`.** -/
def TailSideHyp (n : ℕ) (c α : ℝ) (q : (Fin n → ℤ) → EuclideanSpace ℝ (UT n))
    (W : Finset (Fin n → ℤ)) (A₀ : EuclideanSpace ℝ (UT n)) : Prop :=
  ∀ k, k < ParamsAdopted2.numStepsAdopted2 n → k ≠ 0 → ∀ y ∈ W,
    (gaussPath (EuclideanSpace ℝ (UT n)))
        {ω | ∃ i ≤ k, constraintM q W A₀ (step c) y i ω ≤ 0}
      ≤ ENNReal.ofReal (4 * Phi (yOf (a0C n)
          ((k : ℝ) * ParamsAdopted2.stepSizeAdopted2 n) (α * ‖toE n y‖)))

/-- The **non**-probabilistic arguments of `chainRaw2_of_walk`: §5 arithmetic and the chain's own
lattice data.  Bundled so the composition below has one hypothesis of each kind. -/
structure RawData (p n : ℕ) (α R : ℝ) (q : (Fin n → ℤ) → EuclideanSpace ℝ (UT n))
    (W : Finset (Fin n → ℤ)) (A₀ : EuclideanSpace ℝ (UT n)) : Prop where
  hq : ∀ j : (Fin n → ℤ), ∀ i ∈ W, (0 : ℝ) ≤ ⟪q i, q j⟫
  hA₀ : ∀ y ∈ W, (1 : ℝ) < ⟪A₀, q y⟫
  alpha_pos : 0 < α
  alpha_norm : α ^ n * ((p ^ (n - 1) : ℕ) : ℝ) = kappa n
  R_nonneg : 0 ≤ R
  R_scaled : α * R ≤ 1 - 1 / (n : ℝ)
  R_lt_p : R < (p : ℝ)
  tiling_defect : (n : ℝ) * (α * Real.sqrt n / 2) ≤ 1 / 4
  window_lt_p : windowC α n < (p : ℝ)
  supp_ne_zero : ∀ y ∈ W, y ≠ 0
  supp_radius : ∀ y ∈ W, ‖toE n y‖ ≤ windowC α n
  hwin : ∀ y ∈ W, ‖toE n y‖ + Real.sqrt n / 2 ≤ windowC α n
  hr : ∀ y ∈ W, 0 < α * ‖toE n y‖
  hy : ∀ k, k < ParamsAdopted2.numStepsAdopted2 n → k ≠ 0 → ∀ y ∈ W,
    0 < yOf (a0C n) ((k : ℝ) * ParamsAdopted2.stepSizeAdopted2 n) (α * ‖toE n y‖)
  arith : (n : ℝ) * kappa n * ((p : ℝ) - 1) * (8 - 8 / (n : ℝ) ^ 2) < 8 * ((p : ℝ) ^ n - 1)

/-- **`ChainRaw2` on `chainSetup`.**  The chain is driven by `ChainSetup.step c` on
`gaussPath (EuclideanSpace ℝ (UT n))`; the composition is `chainRaw2_of_walk` with the space, its
probability structure and the driving sequence supplied. -/
noncomputable def chainRaw2_on_setup {n p : ℕ} {c α : ℝ}
    {q : (Fin n → ℤ) → EuclideanSpace ℝ (UT n)} {W : Finset (Fin n → ℤ)}
    {A₀ : EuclideanSpace ℝ (UT n)} {R : ℝ} (hn : 3 ≤ n)
    (hdata : RawData p n α R q W A₀) (htail : TailSideHyp n c α q W A₀) :
    ChainRaw2 p n :=
  chainRaw2_of_walk (P := gaussPath (EuclideanSpace ℝ (UT n))) (ξ := step c)
    hn hdata.hq hdata.hA₀ hdata.alpha_pos hdata.alpha_norm R hdata.R_nonneg
    hdata.R_scaled hdata.R_lt_p hdata.tiling_defect hdata.window_lt_p hdata.supp_ne_zero
    hdata.supp_radius hdata.hwin hdata.hr hdata.hy htail hdata.arith

/-- **The tail-side component of `Theorem.ChainDelivers`**: its fields up to, but not including,
the drift's `Assembly.ChainOutput`. -/
def TailSide : Prop :=
  ∀ m : ℕ, Threshold2.n₁ ≤ m →
    ∃ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p), Nonempty (ChainRaw2 p (m + 1))

/-- **The tail side of `ChainDelivers`, on `chainSetup`.**  Given, at each dimension, the lattice
and arithmetic data and the one probabilistic hypothesis, the chain run on `chainSetup` delivers
the `ChainRaw2` datum. -/
theorem tailSide_on_setup
    (h : ∀ m : ℕ, Threshold2.n₁ ≤ m →
      ∃ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p) (c α R : ℝ)
        (q : (Fin (m + 1) → ℤ) → EuclideanSpace ℝ (UT (m + 1)))
        (W : Finset (Fin (m + 1) → ℤ)) (A₀ : EuclideanSpace ℝ (UT (m + 1))),
        3 ≤ m + 1 ∧ RawData p (m + 1) α R q W A₀ ∧ TailSideHyp (m + 1) c α q W A₀) :
    TailSide := by
  intro m hm
  obtain ⟨p, hp, hp0, c, α, R, q, W, A₀, hn, hdata, htail⟩ := h m hm
  exact ⟨p, hp, hp0, ⟨chainRaw2_on_setup hn hdata htail⟩⟩

end Composition

end

end Submission.L10.PaddedLawSetup

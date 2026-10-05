import Mathlib
import Submission.L10.Theorem
import Submission.L10.RawDataInst2

/-!
# Gate L-10 — the light-contact fact, threaded to the top

Brief 65.  `Section5.exists_good_line_of_chainData` (`:345`) proves **two** things about the line
`g` it chooses: the R-condition, and the light-contact bound
`∑ y ∈ supp.filter (· ∈ latZ p n g), w y < theta` — the entire point of §5's averaging.
`Assembly.exists_phi_of_params` (`:227`) writes `obtain ⟨g, hg0, hfreeR, _⟩` and throws the second
away, so `Theorem.ChainDelivers` asks the drift side for `ChainOutput` for **every** `g` with no
short vectors.  The drift side cannot deliver that: its count bound
(`StateInvariant4.lean:318-319`, `hθ : ∑_{i ∈ W} weight i ≤ θ`) *is* the discarded fact, at
`W_g = supp.filter (· ∈ latZ g)`.  Same shape as report 56 §2's `DriftSide`: a hypothesis that
composes and cannot be proved.

`Assembly.lean` and `Theorem.lean` are reported and are not edited; the threaded copies live here.

* `LightContact` — the discarded fact, named.
* `exists_phi_of_params'`, `remaining_of_lemma43'`, `lemma43_input_of_raw2'` — the three links,
  each the original proof with the `_` kept.
* `params_of_raw2_theta` — `theta` in closed form: `ENNReal.ofReal (64 · C1C α n)`.
* `chainRaw2_on_setup_alpha`/`_R`/`_supp` — the three `rfl`s the composition rests on.
* `ChainDelivers'`, `klartag_packing_of_chain'` — the data-first shape, with `Q` built inside.
-/

set_option linter.unusedSectionVars false

open MeasureTheory Matrix Metric Finset

namespace Submission.L10.Theorem2

open scoped ENNReal RealInnerProductSpace
open Submission.L10 Submission.L10.Increments Submission.L10.Assembly
open Submission.L10.ConstructionA Submission.L10.ChainDataInst Submission.L10.LatticeTransfer
open Submission.L10.Section5 Submission.L10.Tiling Submission.L10.PaddedLawSetup

/-- **The light-contact property** §5 proves and `Assembly.exists_phi_of_params` discards: on the
chosen line `g`, the total contact weight over the window is below Markov's threshold. -/
def LightContact {p m : ℕ} [NeZero p] (w : (Fin (m + 1) → ℤ) → ℝ≥0∞) (supp : Finset (Fin (m + 1) → ℤ))
    (theta : ℝ≥0∞) (g : Fin (m + 1) → ZMod p) : Prop :=
  ∑ y ∈ supp.filter (fun y => y ∈ latZ p (m + 1) g), w y < theta

/-- **`exists_phi_of_params` with the light-contact fact kept.**  The only change is that the
fourth component of `exists_good_line_of_params` is no longer thrown away. -/
theorem exists_phi_of_params' {p m : ℕ} [Fact (Nat.Prime p)] [NeZero p] (P : Params p (m + 1))
    {c₀ : ℝ}
    (hchain : ∀ g : Fin (m + 1) → ZMod p, g ≠ 0 →
      (∀ y : Fin (m + 1) → ℤ, y ≠ 0 → ‖toE (m + 1) y‖ ≤ P.R → y ∉ latZ p (m + 1) g) →
      LightContact P.w P.supp P.theta g →
      ChainOutput P.alpha g c₀) :
    ∃ φ : EuclideanSpace ℝ (Fin (m + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (m + 1)),
      ENNReal.ofReal (c₀ * (m : ℝ) ^ 2) ≤ volume (φ '' Metric.ball 0 1) ∧
      {v ∈ φ '' Metric.ball 0 1 | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} := by
  obtain ⟨g, hg0, hfreeR, hlight⟩ := exists_good_line_of_params P
  obtain ⟨A, S, hApos, hS, heq68, hfree⟩ := hchain g hg0 hfreeR hlight
  obtain ⟨B, hBdet, hBabs, hBmem⟩ :=
    exists_scaled_basisMatrix (p := p) (n := m + 1) (Nat.le_add_left 1 m) P.alpha_pos
      P.alpha_norm hg0
  have hfreeB : ∀ y : Fin (m + 1) → ℤ, y ≠ 0 →
      (WithLp.toLp 2 (B *ᵥ (fun i => (y i : ℝ))) : EuclideanSpace ℝ (Fin (m + 1)))
        ∉ ChainEllipsoid.ellipsoid A := by
    intro y hy
    refine hfree _ (hBmem y) (mulVec_ne_zero hBdet ?_)
    intro hz
    refine hy (funext fun i => ?_)
    have hzi := congrFun hz i
    simp only [Pi.zero_apply] at hzi ⊢
    exact_mod_cast hzi
  obtain ⟨A', S', hA'pos, hS', hvol, hint⟩ :=
    chain_hyp_of_transfer hApos hS hBdet hfreeB (transfer_det_of_eq68 hBabs heq68)
  refine ⟨Matrix.toEuclideanLin S', ?_, ?_⟩
  · rw [ChainEllipsoid.image_ball_eq_ellipsoid hS']
    exact ChainEllipsoid.volume_ellipsoid_ge hA'pos hS' hvol
  · rw [ChainEllipsoid.image_ball_eq_ellipsoid hS']
    exact hint

/-- `Threshold2.remaining_of_lemma43`, threaded. -/
theorem remaining_of_lemma43' {c₀ : ℝ} (hc₀ : 0 < c₀)
    (H : ∀ m : ℕ, Threshold2.n₁ ≤ m →
      ∃ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p) (P : Params p (m + 1)),
        ∀ g : Fin (m + 1) → ZMod p, g ≠ 0 →
          (∀ y : Fin (m + 1) → ℤ, y ≠ 0 → ‖toE (m + 1) y‖ ≤ P.R → y ∉ latZ p (m + 1) g) →
          LightContact P.w P.supp P.theta g →
          ChainOutput P.alpha g c₀) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      let V := EuclideanSpace ℝ (Fin (n + 1))
      ∃ φ : V →ₗ[ℝ] V, let E := φ '' Metric.ball (0 : V) 1
        (MeasureTheory.volume E : EReal) = c * n ^ 2 ∧
        {v ∈ E | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} := by
  refine Threshold.klartag_packing_of_phi (N₁ := Threshold2.n₁) hc₀ ?_
  intro m hm
  obtain ⟨p, hp, hp0, P, hchain⟩ := H m hm
  exact exists_phi_of_params' P hchain

/-! ### 2. `theta` in closed form, and the `ChainRaw2` layer -/

/-- **`Params.theta` unfolds to a closed form in `α` and `n`**: `64·C1C α n`, where `C1C` is
Lemma 4.3's constant.  `w` and `supp` are `Q.w`, `Q.supp` definitionally. -/
theorem params_of_raw2_theta {p n : ℕ} [Fact (Nat.Prime p)] (hn : 2073600 ≤ n)
    (Q : ChainRaw2 p n) :
    (params_of_raw2 hn Q).theta = ENNReal.ofReal (64 * C1C Q.alpha n) := by
  show ENNReal.ofReal (16 * (4 * C1C Q.alpha n)) = _
  congr 1
  ring

/-- `TailAtStep.lemma43_input_of_raw2`, threaded. -/
theorem lemma43_input_of_raw2' {c₀ : ℝ} (hc₀ : 0 < c₀)
    (H : ∀ m : ℕ, Threshold2.n₁ ≤ m →
      ∃ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p) (Q : ChainRaw2 p (m + 1)),
        ∀ g : Fin (m + 1) → ZMod p, g ≠ 0 →
          (∀ y : Fin (m + 1) → ℤ, y ≠ 0 → ‖toE (m + 1) y‖ ≤ Q.R → y ∉ latZ p (m + 1) g) →
          LightContact Q.w Q.supp (ENNReal.ofReal (64 * C1C Q.alpha (m + 1))) g →
          ChainOutput Q.alpha g c₀) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      let V := EuclideanSpace ℝ (Fin (n + 1))
      ∃ φ : V →ₗ[ℝ] V, let E := φ '' Metric.ball (0 : V) 1
        (MeasureTheory.volume E : EReal) = c * n ^ 2 ∧
        {v ∈ E | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} := by
  refine remaining_of_lemma43' hc₀ (fun m hm => ?_)
  have hm' : 2073600 ≤ m + 1 := by
    have : 2073600 ≤ m := by simpa [Threshold2.n₁] using hm
    omega
  obtain ⟨p, hp, hp0, Q, h⟩ := H m hm
  refine ⟨p, hp, hp0, params_of_raw2 hm' Q, fun g hg hfree hlight => ?_⟩
  exact h g hg hfree (by rwa [params_of_raw2_theta] at hlight)

/-! The three identifications the composition rests on, each `rfl`: `chainRaw2_of_walk` passes
`α`, `R`, `W` straight to `chainRaw2_of_chain`, whose fields are `alpha := alpha`, `R := R`,
`supp := supp`. -/

theorem chainRaw2_on_setup_alpha {p n : ℕ} {c α R : ℝ}
    {q : (Fin n → ℤ) → EuclideanSpace ℝ (UT n)} {W : Finset (Fin n → ℤ)}
    {A₀ : EuclideanSpace ℝ (UT n)} (hn : 3 ≤ n) (hdata : RawData p n α R q W A₀)
    (htail : TailSideHyp n c α q W A₀) :
    (chainRaw2_on_setup hn hdata htail).alpha = α := rfl

theorem chainRaw2_on_setup_R {p n : ℕ} {c α R : ℝ}
    {q : (Fin n → ℤ) → EuclideanSpace ℝ (UT n)} {W : Finset (Fin n → ℤ)}
    {A₀ : EuclideanSpace ℝ (UT n)} (hn : 3 ≤ n) (hdata : RawData p n α R q W A₀)
    (htail : TailSideHyp n c α q W A₀) :
    (chainRaw2_on_setup hn hdata htail).R = R := rfl

theorem chainRaw2_on_setup_supp {p n : ℕ} {c α R : ℝ}
    {q : (Fin n → ℤ) → EuclideanSpace ℝ (UT n)} {W : Finset (Fin n → ℤ)}
    {A₀ : EuclideanSpace ℝ (UT n)} (hn : 3 ≤ n) (hdata : RawData p n α R q W A₀)
    (htail : TailSideHyp n c α q W A₀) :
    (chainRaw2_on_setup hn hdata htail).supp = W := rfl

/-- The weight the chain actually produces: `ChainRaw2.w` of `chainRaw2_on_setup`. -/
noncomputable def chainW {p m : ℕ} {α R : ℝ}
    {q : (Fin (m + 1) → ℤ) → EuclideanSpace ℝ (UT (m + 1))} {W : Finset (Fin (m + 1) → ℤ)}
    {A₀ : EuclideanSpace ℝ (UT (m + 1))} (hn : 3 ≤ m + 1)
    (hdata : RawData p (m + 1) α R q W A₀)
    (hnd : TailSideSetup2.NormData (m + 1) α q W A₀) : (Fin (m + 1) → ℤ) → ℝ≥0∞ :=
  (chainRaw2_on_setup hn hdata (TailSideSetup2.tailSideHyp_of_rawData hdata hnd hn)).w

/-! ### 3. `ChainDelivers'`, data first -/

/-- **What the two sides can actually meet in.**  The data comes first, so the drift side is
handed the very `α`, `R`, `q`, `W`, `A₀` the tail side built, and — the point of this module —
the **light-contact** fact §5 proves about the chosen `g`. -/
def ChainDelivers' (c₀ : ℝ) : Prop :=
  ∀ m : ℕ, Threshold2.n₁ ≤ m →
    ∃ (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : NeZero p) (α R : ℝ)
      (q : (Fin (m + 1) → ℤ) → EuclideanSpace ℝ (UT (m + 1))) (W : Finset (Fin (m + 1) → ℤ))
      (A₀ : EuclideanSpace ℝ (UT (m + 1))) (hn : 3 ≤ m + 1)
      (hdata : RawData p (m + 1) α R q W A₀)
      (hnd : TailSideSetup2.NormData (m + 1) α q W A₀),
      ∀ g : Fin (m + 1) → ZMod p, g ≠ 0 →
        (∀ y : Fin (m + 1) → ℤ, y ≠ 0 → ‖toE (m + 1) y‖ ≤ R → y ∉ latZ p (m + 1) g) →
        LightContact (chainW hn hdata hnd) W (ENNReal.ofReal (64 * C1C α (m + 1))) g →
        ChainOutput α g c₀

/-- **The challenge statement from `ChainDelivers'`.**  `Q := chainRaw2_on_setup …` is built here,
and `Q.alpha = α`, `Q.R = R`, `Q.supp = W`, `Q.w = chainW …` all hold by `rfl`. -/
theorem klartag_packing_of_chain' {c₀ : ℝ} (hc₀ : 0 < c₀) (h : ChainDelivers' c₀) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      let V := EuclideanSpace ℝ (Fin (n + 1))
      ∃ φ : V →ₗ[ℝ] V, let E := φ '' Metric.ball (0 : V) 1
        (MeasureTheory.volume E : EReal) = c * n ^ 2 ∧
        {v ∈ E | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} := by
  refine lemma43_input_of_raw2' hc₀ (fun m hm => ?_)
  obtain ⟨p, hp, hp0, α, R, q, W, A₀, hn, hdata, hnd, hgood⟩ := h m hm
  exact ⟨p, hp, hp0,
    chainRaw2_on_setup hn hdata (TailSideSetup2.tailSideHyp_of_rawData hdata hnd hn),
    fun g hg hfree hlight => hgood g hg hfree hlight⟩

end Submission.L10.Theorem2

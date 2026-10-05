/-
Gate L-10 (`klartag_packing`), brief 16.

**Closing Lemma 4.3's interface**: `Params` ↔ `RadialWeightData'`, and the Markov numeric at
Klartag's own threshold.

Reading `ChainDataInst.chainData_of_params` settles one thing immediately: brief 13's `Params`
already carries the whole Lemma 4.3 block as *fields*, and already discharges `supp_indivisible`
from `supp_ne_zero` and `supp_radius` itself.  So the earlier route addition's seam is closed on
both sides, and what is left is to make those fields **constructible** rather than assumed.

`radialWeightData_of_params` below is the projection (no hypotheses beyond `Params`' own fields,
as the brief asks); `Lemma43C.radialWeightData'_of_chain` is the converse.  Between them the
boundary is settled.

**The observation worth carrying.**  Klartag's Markov threshold is `16·C₁·n⁻²·e^{n²T/8}`
(p. 22, eq. 66).  At `T = 16·log n/n²` report 14 proved `e^{n²T/8} = n²` *exactly*, so

  `θ = 16·C₁·n⁻²·n² = 16·C₁`

— an **absolute constant**, with no `n` in it at all.  `klartag_theta_eq` is that identity, and
`markov_of_arith` reduces the Markov field to one inequality in `p`, `n` and `κ_n`.
-/
import Submission.L10.Lemma43C
import Submission.L10.ChainDataInst

namespace Submission.L10

open MeasureTheory Set Real Submission.L10.Section5 Submission.L10.Tiling
open scoped ENNReal NNReal

/-! ## 1. `Params` → `RadialWeightData'`, with no extra hypotheses -/

section Projection

open Submission.L10.ChainDataInst

/-- **The projection.**  Every field of `RadialWeightData'` is a field of `Params`, so this takes
no hypotheses beyond `Params`' own — the shape the brief asked for. -/
def radialWeightData_of_params {p n : ℕ} (P : Params p n) : RadialWeightData' p n where
  f := P.f
  f_nonneg := P.f_nonneg
  w := P.w
  supp := P.supp
  dom := P.dom
  integrable := P.integrable
  C := P.C
  radial_bound := P.radial_bound
  theta := P.theta
  markov := P.markov
  windowRadius := P.windowRadius
  window_lt_p := P.window_lt_p
  supp_ne_zero := P.supp_ne_zero
  supp_radius := P.supp_radius
  theta_ne_zero := P.theta_ne_zero
  theta_ne_top := P.theta_ne_top

/-- `ChainData.weight_bound` straight from `Params`, through this brief's route rather than
`chainData_of_params`' inline call — report 13 §5.3 asked that the two not be duplicated. -/
theorem weight_bound_of_params_proj {p n : ℕ} [Fact (Nat.Prime p)] (hn : 0 < n)
    (P : Params p n) :
    2 * (((p - 1 : ℕ) : ℝ≥0∞) * ∑ y ∈ P.supp, P.w y) < P.theta * ((p ^ n - 1 : ℕ) : ℝ≥0∞) :=
  weight_bound_of_params' hn (radialWeightData_of_params P)

/-- `ChainData.supp_indivisible` through the same route. -/
theorem supp_indivisible_of_params {p n : ℕ} [NeZero p] (P : Params p n) :
    ∀ y ∈ P.supp, ConstructionA.redMod p y ≠ 0 :=
  supp_indivisible_of_data (radialWeightData_of_params P)

end Projection

/-! ## 2. Klartag's Markov threshold is an absolute constant -/

/-- **`θ = 16·C₁`.**  Klartag's threshold `16·C₁·n⁻²·e^{n²T/8}` (p. 22, eq. 66) collapses at
`T = 16·log n/n²`, because `e^{n²T/8} = n²` exactly (report 14's `exp_n2T_eq`).  No `n` survives. -/
theorem klartag_theta_eq {n : ℕ} (hn : 0 < n) {T C₁ : ℝ}
    (hT : T = 16 * Real.log n / (n : ℝ) ^ 2) :
    16 * C₁ / (n : ℝ) ^ 2 * Real.exp ((n : ℝ) ^ 2 / 8 * T) = 16 * C₁ := by
  have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 hn
  have hne : ((n : ℝ)) ^ 2 ≠ 0 := by positivity
  rw [exp_n2T_eq hn hT]
  field_simp

/-! ## 3. The Markov numeric

`markov` is `2·(p−1)·ofReal(n·κ_n·C) < θ·(p^n − 1)` with `C = C₁·(8 − 8/n²)` and, by §2,
`θ = ofReal (16·C₁)`.  Dividing by `C₁ > 0`, it is exactly

  `n·κ_n·(p−1)·(8 − 8/n²) < 8·(p^n − 1)`,

an inequality in `p`, `n` and `κ_n` alone — no analysis left in it.  The `8` on the right is
`16/2`: the Markov field carries a factor `2` on its left, which is Klartag's "twice the first
moment" (eq. 66).  Getting that factor wrong is the easiest slip here, so it is written out. -/

section Markov

/-- Casting `(p − 1 : ℕ)` into `ℝ≥0∞` through the reals. -/
theorem cast_sub_one {p : ℕ} (hp : 1 ≤ p) :
    ((p - 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((p : ℝ) - 1) := by
  rw [← ENNReal.ofReal_natCast]
  congr 1
  have : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    push_cast [Nat.cast_sub hp]; ring
  rw [this]

/-- **The Markov numeric, reduced to arithmetic.**  With `θ = ofReal (16·C₁)` — the absolute
constant of §2 — the Markov field of `Params` holds as soon as

  `n·κ_n·(p−1)·(8 − 8/n²) < 8·(p^n − 1)`.

Everything analytic has been discharged; what remains is a statement about `p`, `n` and the volume
of the unit ball, and it holds for `p` large because `p^n` beats `p` for `n ≥ 2`. -/
theorem markov_of_arith {p n : ℕ} (hn : 0 < n) (hp : 1 ≤ p) (hpn : 1 < p ^ n) {C₁ : ℝ}
    (hC₁ : 0 < C₁)
    (harith : (n : ℝ) * kappa n * ((p : ℝ) - 1) * (8 - 8 / (n : ℝ) ^ 2)
      < 8 * ((p : ℝ) ^ n - 1)) :
    2 * (((p - 1 : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal ((n : ℝ) * kappa n * (C₁ * (8 - 8 / (n : ℝ) ^ 2))))
      < ENNReal.ofReal (16 * C₁) * ((p ^ n - 1 : ℕ) : ℝ≥0∞) := by
  have hp1 : (0 : ℝ) ≤ (p : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  have hpn1 : (0 : ℝ) < (p : ℝ) ^ n - 1 := by
    have : (1 : ℝ) < (p : ℝ) ^ n := by exact_mod_cast hpn
    linarith
  have hcastpn : ((p ^ n - 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((p : ℝ) ^ n - 1) := by
    rw [← ENNReal.ofReal_natCast]
    congr 1
    have : ((p ^ n - 1 : ℕ) : ℝ) = (p : ℝ) ^ n - 1 := by
      push_cast [Nat.cast_sub hpn.le]; ring
    rw [this]
  have hk : (0 : ℝ) ≤ (n : ℝ) * kappa n := by
    have := kappa_nonneg n
    positivity
  have h8 : (0 : ℝ) ≤ 8 - 8 / (n : ℝ) ^ 2 := eight_sub_nonneg hn
  rw [cast_sub_one hp, hcastpn, ← ENNReal.ofReal_mul hp1,
    show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  refine (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 ?_
  nlinarith [harith, hC₁, hk, h8, hp1, hpn1]

end Markov

/-! ## 4. The integrability certificates

Three of `radialWeightData'_of_chain`'s five hypotheses are integrability.  All three have the same
two reasons behind them — the profile is **bounded** (by `Φ ≤ 1/2`) and **supported in a bounded
window** — so both are isolated here once and instantiated three times. -/

section Integrability

/-- Bounded and measurable on a finite-measure set is integrable there. -/
theorem integrableOn_of_bounded' {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    {f : α → ℝ} (hsm : MeasurableSet s) (hs : μ s ≠ ⊤) (hm : AEStronglyMeasurable f μ) {M : ℝ}
    (hb : ∀ x ∈ s, ‖f x‖ ≤ M) : IntegrableOn f s μ := by
  refine Measure.integrableOn_of_bounded (s_finite := hs) (f_mble := hm) (M := M) ?_
  filter_upwards [self_mem_ae_restrict hsm] with x hx
  exact hb x hx

/-- **`hgt`, discharged.**  The fixed-radius slice `t ↦ g t r` is integrable on `(0,T]` because it
is bounded and `(0,T]` has finite measure.  `Φ ≤ 1/2` supplies the bound. -/
theorem integrableOn_t_of_bounded {T : ℝ} {g : ℝ → ℝ → ℝ} {M : ℝ}
    (hm : ∀ r : ℝ, AEStronglyMeasurable (fun t : ℝ => g t r) volume)
    (hb : ∀ t ∈ Ioc (0 : ℝ) T, ∀ r : ℝ, ‖g t r‖ ≤ M) (r : ℝ) :
    IntegrableOn (fun t : ℝ => g t r) (Ioc (0 : ℝ) T) :=
  integrableOn_of_bounded' measurableSet_Ioc (by simp [Real.volume_Ioc]) (hm r)
    (fun t ht => hb t ht r)

/-- **Extending integrability from a bounded window to `(0,∞)`.**  A profile supported in
`(0, L]` is integrable on `Ioi 0` as soon as it is integrable on the window.  This is what turns
the fixed-window bound into `RadialWeightData.radial_bound`'s `Ioi 0` statement. -/
theorem integrableOn_Ioi_of_support {f : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf : IntegrableOn f (Ioc (0 : ℝ) L)) (hzero : ∀ y : ℝ, L < y → f y = 0) :
    IntegrableOn f (Ioi (0 : ℝ)) := by
  have hsplit : Ioi (0 : ℝ) = Ioc (0 : ℝ) L ∪ Ioi L := (Ioc_union_Ioi_eq_Ioi hL).symm
  have htail : IntegrableOn f (Ioi L) := by
    have h0 : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Ioi L) volume := integrableOn_zero
    refine h0.congr_fun ?_ measurableSet_Ioi
    intro y hy
    exact (hzero y hy).symm
  rw [hsplit]
  exact hf.union htail

end Integrability

end Submission.L10

/-
Gate L-10 (`klartag_packing`), brief 96b — the expected shortfall `E[(L − X)⁺]` from a PATHWISE
lower bound on `X`, with no mean, no tail and no Chebyshev.

**What this replaces.**  `GoodPathVar.shortfall_le_of_variance` (brief 94b) needs three things the
chain cannot cheaply supply: `hmean` (`L ≤ E X`, i.e. a *lower* bound on the mean log-determinant),
`htail` (`P(X ≤ L) ≤ r`), and the variance around the mean.  All three disappear once the pathwise
lower bound of `LogDetLowerSharp` is in hand: writing

  `X ≥ c + M − D`   pointwise,  `L := c − dbar − t`,

the shortfall splits with no probability at all,

  `(L − X)⁺ ≤ (−M)⁺ + (D − dbar)⁺`,

and each half is closed by one application of `u ≤ u²/(4t) + t`.  `c` is `logDet A₀`, `M` the
martingale `∑⟪V_k, ξ_k⟫`, `D` the drift proxy `κ·∑‖π_kξ_k‖²`, and `dbar` any constant above `E D`.

**Why `(D − dbar)⁺` and not `D`.**  Charging the whole of `E D` to the shortfall costs
`κ·T·dim = O(log n)`, which grows and eventually breaks the budget; charging only the excess over
`dbar` costs `O(1)`.  This is the same distinction that kills the plain-floor route, one level down.

Nothing reported is edited.
-/
import Submission.L10.GoodPathVar

set_option linter.unusedSectionVars false

namespace Submission.L10.ShortfallBound

open MeasureTheory

/-! ## 1. The two scalar inequalities -/

/-- **`u⁺ ≤ u²/(4t) + t`** for `t > 0`, every real `u`.  At `u > 0` it is `(u − 2t)² ≥ 0`. -/
theorem pos_part_le_sq_add {u t : ℝ} (ht : 0 < t) : max u 0 ≤ u ^ 2 / (4 * t) + t := by
  by_cases h : u ≤ 0
  · rw [max_eq_right h]; positivity
  · rw [max_eq_left ((not_le.mp h).le), ← sub_nonneg]
    have hkey : u ^ 2 / (4 * t) + t - u = (u - 2 * t) ^ 2 / (4 * t) := by
      field_simp; ring
    rw [hkey]; positivity

/-- **`(u − t)⁺ ≤ u²/(4t)`** for `t > 0`, every real `u`.  The shifted form, with no additive `t`
left over: it is what the drift's excess uses, where the shift is already paid for inside `L`. -/
theorem pos_part_sub_le_sq {u t : ℝ} (ht : 0 < t) : max (u - t) 0 ≤ u ^ 2 / (4 * t) := by
  by_cases h : u - t ≤ 0
  · rw [max_eq_right h]; positivity
  · rw [max_eq_left ((not_le.mp h).le), ← sub_nonneg]
    have hkey : u ^ 2 / (4 * t) - (u - t) = (u - 2 * t) ^ 2 / (4 * t) := by
      field_simp; ring
    rw [hkey]; positivity

/-! ## 2. The pathwise split -/

section Split

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The shortfall splits along a pathwise lower bound.**  No integrability and no measurability:
this is an inequality of functions. -/
theorem pos_part_shortfall_le {X M D : Ω → ℝ} {c dbar t : ℝ} (ht : 0 ≤ t)
    (hlow : ∀ ω, c + M ω - D ω ≤ X ω) (ω : Ω) :
    max ((c - dbar - t) - X ω) 0 ≤ max (-(M ω)) 0 + max (D ω - dbar) 0 := by
  have h1 : (c - dbar - t) - X ω ≤ -(M ω) + (D ω - dbar) := by linarith [hlow ω]
  have h2 : -(M ω) ≤ max (-(M ω)) 0 := le_max_left _ _
  have h3 : D ω - dbar ≤ max (D ω - dbar) 0 := le_max_left _ _
  have h4 : (0 : ℝ) ≤ max (-(M ω)) 0 + max (D ω - dbar) 0 :=
    add_nonneg (le_max_right _ _) (le_max_right _ _)
  exact max_le (by linarith) h4

/-- **The shortfall bound.**  `a` closes the martingale half, `b` the drift-excess half. -/
theorem integral_shortfall_le {X M D : Ω → ℝ} {c dbar t a b : ℝ} (ht : 0 ≤ t)
    (hlow : ∀ ω, c + M ω - D ω ≤ X ω)
    (hMi : Integrable (fun ω => max (-(M ω)) 0) P)
    (hDi : Integrable (fun ω => max (D ω - dbar) 0) P)
    (hMs : Integrable (fun ω => max ((c - dbar - t) - X ω) 0) P)
    (hM : ∫ ω, max (-(M ω)) 0 ∂P ≤ a) (hD : ∫ ω, max (D ω - dbar) 0 ∂P ≤ b) :
    ∫ ω, max ((c - dbar - t) - X ω) 0 ∂P ≤ a + b := by
  have hle : ∫ ω, max ((c - dbar - t) - X ω) 0 ∂P
      ≤ ∫ ω, (max (-(M ω)) 0 + max (D ω - dbar) 0) ∂P :=
    integral_mono hMs (hMi.add hDi) (fun ω => pos_part_shortfall_le ht hlow ω)
  rw [integral_add hMi hDi] at hle
  linarith

end Split

/-! ## 3. The two halves, from second moments -/

section Halves

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The martingale half**: `E[(−M)⁺] ≤ v/(4t) + t` from `E[M²] ≤ v` alone — no mean-zero
hypothesis, no tail, no Cauchy–Schwarz.  At the chain `v = varBound n c₃ ≈ 1.4·10⁻⁴`, so `t = 0.01`
gives `0.0135` and `t = √v/2` gives `√v ≈ 0.012`. -/
theorem integral_neg_part_le {M : Ω → ℝ} {v t : ℝ} (ht : 0 < t)
    (hMi : Integrable (fun ω => max (-(M ω)) 0) P)
    (hsq : Integrable (fun ω => M ω ^ 2) P) (hv : ∫ ω, M ω ^ 2 ∂P ≤ v) :
    ∫ ω, max (-(M ω)) 0 ∂P ≤ v / (4 * t) + t := by
  have hint : Integrable (fun ω => (-(M ω)) ^ 2 / (4 * t) + t) P := by
    have hf : (fun ω => (-(M ω)) ^ 2 / (4 * t) + t) = (fun ω => M ω ^ 2 / (4 * t) + t) := by
      funext ω; ring_nf
    rw [hf]; exact (hsq.div_const _).add (integrable_const t)
  have hmono : ∫ ω, max (-(M ω)) 0 ∂P ≤ ∫ ω, ((-(M ω)) ^ 2 / (4 * t) + t) ∂P :=
    integral_mono hMi hint (fun ω => pos_part_le_sq_add ht)
  have hfun : (fun ω => (-(M ω)) ^ 2 / (4 * t) + t) = (fun ω => M ω ^ 2 / (4 * t) + t) := by
    funext ω; ring_nf
  have heq : ∫ ω, ((-(M ω)) ^ 2 / (4 * t) + t) ∂P = (∫ ω, M ω ^ 2 ∂P) / (4 * t) + t := by
    rw [hfun, integral_add (hsq.div_const _) (integrable_const t), integral_div, integral_const]
    simp
  rw [heq] at hmono
  have h4t : (0 : ℝ) < 4 * t := by linarith
  have hdiv : (∫ ω, M ω ^ 2 ∂P) / (4 * t) ≤ v / (4 * t) := by gcongr
  linarith

/-- **The drift-excess half**: `E[(D − dbar)⁺] ≤ w/(4s)` where `dbar` sits `s` above the centre
and `w` bounds the centred second moment.  The chain's `D` is `κ·∑‖π_kξ_k‖²`, whose centre is
`κ·h·E[∑ rank π_k]` and whose excess over `κ·T·dim` is bounded by the light-contact budget. -/
theorem integral_drift_excess_le {D : Ω → ℝ} {cen s w : ℝ} (hs : 0 < s)
    (hDi : Integrable (fun ω => max (D ω - (cen + s)) 0) P)
    (hsq : Integrable (fun ω => (D ω - cen) ^ 2) P)
    (hw : ∫ ω, (D ω - cen) ^ 2 ∂P ≤ w) :
    ∫ ω, max (D ω - (cen + s)) 0 ∂P ≤ w / (4 * s) := by
  have hmono : ∫ ω, max (D ω - (cen + s)) 0 ∂P
      ≤ ∫ ω, ((D ω - cen) ^ 2 / (4 * s)) ∂P := by
    refine integral_mono hDi (hsq.div_const _) (fun ω => ?_)
    have heq : D ω - (cen + s) = (D ω - cen) - s := by ring
    rw [heq]
    exact pos_part_sub_le_sq hs
  rw [integral_div] at hmono
  have h4s : (0 : ℝ) < 4 * s := by linarith
  have hdiv : (∫ ω, (D ω - cen) ^ 2 ∂P) / (4 * s) ≤ w / (4 * s) := by gcongr
  linarith

end Halves

/-! ## 4. `hshort` in the shape `GoodPathVar.exists_mem_of_variance` binds -/

section Assembly

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **`hshort`, assembled.**  `L = c − (cen + s) − t`, and the shortfall is `v/(4t') + t' + w/(4s)`
with `t'` free.  Every input is a second moment of a *centred* quantity; nothing here needs the
mean of `X`, the lower tail of `X`, or Chebyshev. -/
theorem shortfall_le {X M D : Ω → ℝ} {c cen s t t' v w : ℝ} (ht : 0 ≤ t) (ht' : 0 < t')
    (hs : 0 < s)
    (hlow : ∀ ω, c + M ω - D ω ≤ X ω)
    (hMi : Integrable (fun ω => max (-(M ω)) 0) P)
    (hDi : Integrable (fun ω => max (D ω - (cen + s)) 0) P)
    (hXi : Integrable (fun ω => max ((c - (cen + s) - t) - X ω) 0) P)
    (hMsq : Integrable (fun ω => M ω ^ 2) P) (hv : ∫ ω, M ω ^ 2 ∂P ≤ v)
    (hDsq : Integrable (fun ω => (D ω - cen) ^ 2) P) (hw : ∫ ω, (D ω - cen) ^ 2 ∂P ≤ w) :
    ∫ ω, max ((c - (cen + s) - t) - X ω) 0 ∂P ≤ (v / (4 * t') + t') + w / (4 * s) :=
  integral_shortfall_le (dbar := cen + s) ht hlow hMi hDi hXi
    (integral_neg_part_le ht' hMi hMsq hv)
    (integral_drift_excess_le hs hDi hDsq hw)

end Assembly

end Submission.L10.ShortfallBound

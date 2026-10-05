/-
Gate L-10 (`klartag_packing`), brief 96b — the drift proxy's centred second moment, **without any
Gaussian moment computation**.

Report 96b §6 item 3 named one remaining atom: a fourth moment `E‖ξ‖⁴ ≤ 3h²d²`, for which this
Mathlib pin has no lemma (`mgf_gaussianReal` exists; no moment lemma for `stdGaussian` does).
**It is not needed.**  The chain's own good event already bounds the raw step pathwise,
`‖ξ_j‖ ≤ η` for every `j < K` — that is the very hypothesis `GoodPathBounds.stateBounds_goodCut`
reads off `goodCut` before projecting — so each summand of the drift proxy lies in a bounded
interval, and Mathlib's **Popoviciu** inequality (`variance_le_sq_of_bounded`) plus
**`IndepFun.variance_sum`** give the centred second moment with no density, no MGF and no
integration by parts.

Sizes at the adopted parameters: each summand is capped by `η² = 2·h·dim·n`, so the sum of `K ≈ N`
variances is at most `N·η⁴/4 = T·h·dim²·n²`, about `4·log n·n^{-5}` — against a budget where
anything under `0.1` is free.  The truncation `min(‖ξ_j‖², cap)` is what makes the cap hold
everywhere rather than only on the good event; it only ever *lowers* the summand, and the two agree
on the good event, which is where the existence step reads the path.

Nothing reported is edited.
-/
import Submission.L10.ShortfallBound

set_option linter.unusedSectionVars false

namespace Submission.L10.DriftVarianceBounded

open MeasureTheory ProbabilityTheory Finset

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-! ## 1. A bounded summand has a bounded variance, and independence adds them -/

/-- **Popoviciu, per summand.** -/
theorem variance_trunc_le {Z : Ω → ℝ} {cap : ℝ}
    (hZm : AEMeasurable Z P) (hZ : ∀ᵐ ω ∂P, Z ω ∈ Set.Icc (0 : ℝ) cap) :
    variance Z P ≤ (cap / 2) ^ 2 := by
  have h := variance_le_sq_of_bounded hZ hZm
  simpa using h

/-- **The drift proxy's variance**, from independence and a pathwise cap.  No Gaussian moment of
any order is used. -/
theorem variance_sum_le {Z : ℕ → Ω → ℝ} {K : ℕ} {cap : ℝ}
    (hmem : ∀ j ∈ Finset.range K, MemLp (Z j) 2 P)
    (hindep : Set.Pairwise (↑(Finset.range K)) fun i j => IndepFun (Z i) (Z j) P)
    (hZ : ∀ j ∈ Finset.range K, ∀ᵐ ω ∂P, Z j ω ∈ Set.Icc (0 : ℝ) cap) :
    variance (fun ω => ∑ j ∈ Finset.range K, Z j ω) P ≤ (K : ℝ) * (cap / 2) ^ 2 := by
  have hfun : (fun ω => ∑ j ∈ Finset.range K, Z j ω) = ∑ j ∈ Finset.range K, Z j := by
    funext ω; simp
  rw [hfun, IndepFun.variance_sum hmem hindep]
  calc ∑ j ∈ Finset.range K, variance (Z j) P
      ≤ ∑ _j ∈ Finset.range K, (cap / 2) ^ 2 :=
        Finset.sum_le_sum fun j hj =>
          variance_trunc_le ((hmem j hj).aestronglyMeasurable.aemeasurable) (hZ j hj)
    _ = (K : ℝ) * (cap / 2) ^ 2 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-! ## 2. `hw` in the shape `ShortfallBound.integral_drift_excess_le` binds -/

/-- **From the variance to `∫ (D − cen)²`** at a constant `cen` of the caller's choosing: the mean
is the minimiser, so any `cen` with `(E D − cen)² ≤ g` works and `E D` never has to be computed.
This is `VarianceExport.integral_sub_mean_sq_le_of_const` run in the other direction. -/
theorem integral_sub_const_sq_le {D : Ω → ℝ} {cen v g : ℝ}
    (hD : MemLp D 2 P) (hv : variance D P ≤ v) (hg : ((∫ ω, D ω ∂P) - cen) ^ 2 ≤ g) :
    ∫ ω, (D ω - cen) ^ 2 ∂P ≤ v + g := by
  have hDi : Integrable D P := hD.integrable (by norm_num)
  set m : ℝ := ∫ ω, D ω ∂P with hm
  set f : Ω → ℝ := fun ω => (D ω - m) ^ 2 with hf
  set k : Ω → ℝ := fun ω => (D ω - m) * (2 * (m - cen)) with hk
  have hsq : Integrable f P := by
    rw [hf]; exact (hD.sub (memLp_const _)).integrable_sq
  have hcross : Integrable k P := by
    rw [hk]; exact (hDi.sub (integrable_const _)).mul_const _
  have hcongr : ∫ ω, (D ω - cen) ^ 2 ∂P = ∫ ω, (f ω + k ω + (m - cen) ^ 2) ∂P :=
    integral_congr_ae (by filter_upwards with ω using by rw [hf, hk]; ring)
  have hAB : Integrable (fun ω => f ω + k ω) P := hsq.add hcross
  have hstep1 : ∫ ω, (f ω + k ω + (m - cen) ^ 2) ∂P
      = (∫ ω, (f ω + k ω) ∂P) + (m - cen) ^ 2 := by
    rw [integral_add (f := fun ω => f ω + k ω) (g := fun _ => (m - cen) ^ 2) hAB
      (integrable_const _), integral_const]
    simp
  have hstep2 : ∫ ω, (f ω + k ω) ∂P = (∫ ω, f ω ∂P) + ∫ ω, k ω ∂P :=
    integral_add hsq hcross
  have hstep : ∫ ω, (f ω + k ω + (m - cen) ^ 2) ∂P
      = (∫ ω, f ω ∂P) + (∫ ω, k ω ∂P) + (m - cen) ^ 2 := by
    rw [hstep1, hstep2]
  have hzero : ∫ ω, k ω ∂P = 0 := by
    rw [hk, integral_mul_const, integral_sub hDi (integrable_const _), integral_const]
    simp [← hm]
  have hvar : ∫ ω, f ω ∂P = variance D P := by
    rw [hf, hm]
    exact (variance_eq_integral hD.aestronglyMeasurable.aemeasurable).symm
  rw [hcongr, hstep, hzero, hvar]
  linarith

end Submission.L10.DriftVarianceBounded

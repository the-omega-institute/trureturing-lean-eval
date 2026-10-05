-- Vendored from kimihiro64/bombieri-vinogradov@7a174830 BombieriVinogradov/Proof/SiegelWalfisz/ExplicitFormula/PerronError/Estimate/PointwiseAssembly.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.EndpointBound
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.FarSum
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.LowerNearTerm
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.NearBounds
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.UpperNearTerm

/-!
# Pointwise assembly of the Perron ranges

This module classifies every natural index into the far range, the lower or
upper central range, or the singleton endpoint, and assembles their bounds.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- Every source majorant term is bounded by the sum of the four disjoint
range majorants. -/
theorem sourcePerronErrorMajorantTerm_le_decomposition
    {x : Nat} (hx : 0 < x) {c T : Real}
    (hc0 : 0 <= c) (hc3 : c <= 3) (hT : 0 < T) (n : Nat) :
    sourcePerronErrorMajorantTerm x c T n <=
      farSourcePerronErrorTerm x c T n +
        lowerNearPerronBound x T n +
        endpointPerronBound x c T n +
        upperNearPerronBound x T n := by
  by_cases hfar : n <= x / 2 \/ 2 * x <= n
  case pos =>
    rw [farSourcePerronErrorTerm, ite_eq_left hfar]
    have hLower := lowerNearPerronBound_nonneg hx hT n
    have hEndpoint := endpointPerronBound_nonneg x hc0 hT n
    have hUpper := upperNearPerronBound_nonneg hx hT n
    linarith
  case neg =>
    rw [farSourcePerronErrorTerm, ite_eq_right hfar]
    by_cases hnZero : n = 0
    case pos =>
      subst n
      have hxNe : Ne 0 x := Ne.symm (Nat.ne_of_gt hx)
      have hLower := lowerNearPerronBound_nonneg hx hT 0
      simpa [sourcePerronErrorMajorantTerm, endpointPerronBound,
        upperNearPerronBound, hxNe] using hLower
    case neg =>
      have hn : 0 < n := Nat.pos_of_ne_zero hnZero
      rcases lt_trichotomy n x with hnx | hnx | hxn
      case inl =>
        have hnHalf : x / 2 < n := by
          by_contra hnot
          exact hfar (Or.inl (Nat.le_of_not_gt hnot))
        have hBound := sourcePerronErrorMajorantTerm_le_lowerNear
          hn hnHalf hnx hc0 hc3 hT
        have hne : Ne n x := Nat.ne_of_lt hnx
        have hnotUpper : Not (And (x < n) (n <= 2 * x)) := by
          intro h
          exact (Nat.not_lt_of_ge hnx.le) h.1
        rw [lowerNearPerronBound, ite_eq_left hnx,
          endpointPerronBound, ite_eq_right hne,
          upperNearPerronBound, ite_eq_right hnotUpper]
        simpa only [zero_add, add_zero] using hBound
      case inr.inl =>
        subst n
        have hnotLower : Not (x < x) := Nat.lt_irrefl x
        have hnotUpper : Not (And (x < x) (x <= 2 * x)) := by
          intro h
          exact hnotLower h.1
        rw [lowerNearPerronBound, ite_eq_right hnotLower,
          endpointPerronBound, ite_eq_left rfl,
          upperNearPerronBound, ite_eq_right hnotUpper]
        simpa only [zero_add, add_zero] using
          le_of_eq (sourcePerronErrorMajorantTerm_self hx c T)
      case inr.inr =>
        have hnTwice : n <= 2 * x := by
          by_contra hnot
          exact hfar (Or.inr (Nat.le_of_not_ge hnot))
        have hBound := sourcePerronErrorMajorantTerm_le_upperNear
          hx hxn hnTwice hc0 hT
        have hnotLower : Not (n < x) := Nat.not_lt_of_ge hxn.le
        have hne : Ne n x := Ne.symm (Nat.ne_of_lt hxn)
        have hnear : And (x < n) (n <= 2 * x) := And.intro hxn hnTwice
        rw [lowerNearPerronBound, ite_eq_right hnotLower,
          endpointPerronBound, ite_eq_right hne,
          upperNearPerronBound, ite_eq_left hnear]
        simpa only [zero_add, add_zero] using hBound

end BombieriVinogradov.SiegelWalfisz

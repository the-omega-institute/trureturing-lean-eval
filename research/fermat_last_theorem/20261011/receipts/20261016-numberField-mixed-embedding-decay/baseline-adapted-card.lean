import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_NumberField_mixedEmbedding_exists_forall_tsum_fractionalIdeal_weight_le_rpow_neg

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open NumberField
open scoped Classical in

theorem NumberField.mixedEmbedding.exists_forall_tsum_fractionalIdeal_weight_le_rpow_neg
    (F : Type) [Field F] [NumberField F]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (k N' : ℕ) (t₀ : ℝ) (ht₀ : 0 < t₀) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ C : ℝ, ∀ t : ℝ, t₀ ≤ t →
      Summable (fun ξ : {ξ : F // ξ ≠ 0 ∧ ξ ∈ I} =>
        (max 1 ((|Algebra.norm ℚ ξ.1| : ℚ) : ℝ)) ^ k *
          (∏ w : {w : InfinitePlace F // w.IsReal}, (1 + t * |(mixedEmbedding F ξ.1).1 w|) ^ (-(N : ℝ))) *
          ∏ w : {w : InfinitePlace F // w.IsComplex}, (1 + t * ‖(mixedEmbedding F ξ.1).2 w‖) ^ (-(2 * N : ℝ))) ∧
      ∑' ξ : {ξ : F // ξ ≠ 0 ∧ ξ ∈ I},
        (max 1 ((|Algebra.norm ℚ ξ.1| : ℚ) : ℝ)) ^ k *
          (∏ w : {w : InfinitePlace F // w.IsReal}, (1 + t * |(mixedEmbedding F ξ.1).1 w|) ^ (-(N : ℝ))) *
          ∏ w : {w : InfinitePlace F // w.IsComplex}, (1 + t * ‖(mixedEmbedding F ξ.1).2 w‖) ^ (-(2 * N : ℝ))
        ≤ C * t ^ (-(N' : ℝ)) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_mixedEmbedding_exists_forall_tsum_fractionalIdeal_weight_le_rpow_neg.solution

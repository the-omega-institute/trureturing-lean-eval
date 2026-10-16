import Mathlib
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_Rat_hilbertReciprocity_even_card_not_ternary_isotropic

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

open IsDedekindDomain NumberField
theorem Rat.hilbertReciprocity_even_card_not_ternary_isotropic
    (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)),
      (∀ v, v ∈ S ↔
        ¬ ∃ z x y : v.adicCompletion ℚ, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
          z ^ 2 - (algebraMap ℚ (v.adicCompletion ℚ) a) * x ^ 2
            - (algebraMap ℚ (v.adicCompletion ℚ) b) * y ^ 2 = 0) ∧
      Even (S.card + if (a < 0 ∧ b < 0) then 1 else 0) := by p2m_exact_reverting @_root_.P2MW.S_Rat_hilbertReciprocity_even_card_not_ternary_isotropic.solution

import Mathlib
import Submission.Supplier.Definitions.Def_NumberField_PlaceAbove
import Submission.Supplier.Definitions.Def_NumberField_PlaceDecompositionAction
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_NumberField_PlaceDecomp_card_over_fixedField_eq_card_orbitRel_quotient

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false
open IsDedekindDomain NumberField
theorem NumberField.PlaceDecomp.card_over_fixedField_eq_card_orbitRel_quotient (E K : Type) [Field E] [NumberField E] [Field K]
    [NumberField K] [Algebra E K] [IsGalois E K] (S : Finset (HeightOneSpectrum (𝓞 E))) (H : Subgroup (K ≃ₐ[E] K)) :
    Nat.card {u : HeightOneSpectrum (𝓞 (IntermediateField.fixedField H)) // u.under (𝓞 E) ∈ S} =
      Nat.card (MulAction.orbitRel.Quotient H
        (Σ v : S, (K ≃ₐ[E] K) ⧸ NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v))) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_PlaceDecomp_card_over_fixedField_eq_card_orbitRel_quotient.solution

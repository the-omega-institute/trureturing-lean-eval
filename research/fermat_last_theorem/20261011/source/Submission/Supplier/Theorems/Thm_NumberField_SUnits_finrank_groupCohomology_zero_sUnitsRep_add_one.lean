import Mathlib
import Submission.Supplier.Definitions.Def_NumberField_SUnitsModule
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_NumberField_SUnits_finrank_groupCohomology_zero_sUnitsRep_add_one

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false
open IsDedekindDomain NumberField
theorem NumberField.SUnits.finrank_groupCohomology_zero_sUnitsRep_add_one (E K : Type) [Field E] [Field K]
    [NumberField K] [Algebra E K] (S : Finset (HeightOneSpectrum (𝓞 E))) (H : Subgroup (K ≃ₐ[E] K)) :
    Module.finrank ℤ (groupCohomology (Rep.res H.subtype (NumberField.SUnits.sUnitsRep E K S)) 0) + 1 =
      Nat.card {u : HeightOneSpectrum (𝓞 (IntermediateField.fixedField H)) // u.under (𝓞 E) ∈ S} +
        Nat.card (InfinitePlace (IntermediateField.fixedField H)) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_SUnits_finrank_groupCohomology_zero_sUnitsRep_add_one.solution

import Mathlib
import Submission.Supplier.Definitions.Def_GroupCohomology_ContinuousUnramified
import Submission.Supplier.Definitions.Def_DualSelmer_ExtConditions
import Submission.Supplier.Definitions.Def_ExtCitation_KummerBridge
import Submission.Supplier.Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Submission.Supplier.Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Submission.Supplier.Definitions.Def_NumberField_LevelArithmeticModP
import Submission.Supplier.Definitions.Def_NumberField_SelmerRepModP
import Submission.Supplier.Definitions.Def_NumberField_SUnitsMax
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_NumberField_LevelArith_exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
attribute [-instance] AlgebraicClosure.Rat.isGalois

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith
open scoped Classical NumberField NumberField.LevelArith TensorProduct Pointwise

theorem NumberField.LevelArith.exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S) [FiniteDimensional ℚ ↥L] :
    ∃ f : ↥(continuousH1Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) →ₗ[ℤ] (sClassGroupRep ↥L ↥L (S : Set Nat.Primes)),
      Function.Injective f ∧
        Submodule.map f (Submodule.torsionBy ℤ ↥(continuousH1Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) (p : ℤ)) =
          Submodule.torsionBy ℤ (sClassGroupRep ↥L ↥L (S : Set Nat.Primes)) (p : ℤ) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_LevelArith_exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective.solution

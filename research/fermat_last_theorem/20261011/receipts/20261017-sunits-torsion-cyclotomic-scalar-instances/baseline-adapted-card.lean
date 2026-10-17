import Mathlib
import Submission.Supplier.Definitions.Def_GroupCohomology_ContinuousUnramified
import Submission.Supplier.Definitions.Def_DualSelmer_ExtConditions
import Submission.Supplier.Definitions.Def_ExtCitation_KummerBridge
import Submission.Supplier.Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Submission.Supplier.Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Submission.Supplier.Definitions.Def_NumberField_LevelArithmeticModP
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_NumberField_LevelArith_nonempty_inflLevel_repTorsionP_sUnitsRep_iso_twist_cycloChar

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith
open scoped Classical NumberField.LevelArith

theorem NumberField.LevelArith.nonempty_inflLevel_repTorsionP_sUnitsRep_iso_twist_cycloChar
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L]
    (hKL : K ≤ L) [Normal ↥K ↥(levelField K L hKL)]
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p) (hζL : ζ ∈ L) :
    Nonempty (inflLevel K L hKL (repTorsionP p
        (NumberField.SUnits.sUnitsRep ↥K ↥(levelField K L hKL) (placesOverPrimesFinset ↥K S))) ≅
      (Rep.trivial (ZMod p) ↥K.fixingSubgroup (ZMod p)).twist ((cycloChar p).comp K.fixingSubgroup.subtype)) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_LevelArith_nonempty_inflLevel_repTorsionP_sUnitsRep_iso_twist_cycloChar.solution

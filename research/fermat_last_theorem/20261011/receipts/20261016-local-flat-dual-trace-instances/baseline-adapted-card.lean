import Mathlib
import Submission.Supplier.Definitions.Def_GaloisRep_AdZero
import Submission.Supplier.Definitions.Def_GroupCohomology_TangentSpace
import Submission.Supplier.Definitions.Def_ExtEndgame_ProductionDatum
import Submission.Supplier.Definitions.Def_GaloisRep_LocalFlatClasses
import Submission.Supplier.Definitions.Def_GaloisRep_CompletionBridge
import Submission.Supplier.Definitions.Def_FLTPrelim_Ramification
import Submission.Supplier.Definitions.Def_HopfAlgebra_CartierDual
import Submission.Supplier.Definitions.Def_ExtCitation_KummerBridge
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_ResidualGaloisRep_nonempty_localFlatClassesAd_linearEquiv_of_dualTwist

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation

theorem ResidualGaloisRep.nonempty_localFlatClassesAd_linearEquiv_of_dualTwist
    {k : Type} [Field k] [Finite k] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [CharP k p]
    [Algebra ℤ_[p] (ZMod p)] (hker : RingHom.ker (algebraMap ℤ_[p] (ZMod p)) = Ideal.span {(p : ℤ_[p])})
    (ρbar : ResidualGaloisRep k)
    (ρbar' : ResidualGaloisRep k) (η : ρbar'.V ≃ₗ[k] Module.Dual k ρbar.V)
    (hη : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (w : ρbar'.V),
      η (ρbar'.ρ g w) =
        (ZMod.castHom (dvd_refl p) k ((cycloChar p g : (ZMod p)ˣ) : ZMod p)) • ((η w) ∘ₗ (ρbar.ρ g⁻¹))) :
    Nonempty ((ρbar.localFlatClassesAd p) ≃ₗ[k] (ρbar'.localFlatClassesAd p)) := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_nonempty_localFlatClassesAd_linearEquiv_of_dualTwist.solution

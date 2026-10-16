import Mathlib
import Submission.Supplier.Definitions.Def_GaloisRep_Adic
import Submission.Supplier.Definitions.Def_Deformations_ProartinianCat
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_GaloisRepAdic_continuous_unitsMap_toMatrix_of_isAdicContinuous

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open IsLocalRing
theorem GaloisRepAdic.continuous_unitsMap_toMatrix_of_isAdicContinuous
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
    (A : Deformation.ProartinianCat 𝒪) [IsLocalRing.IsAdicTopology A]
    (ρ : GaloisRepAdic A) (b : Module.Basis (Fin 2) A ρ.V) :
    Continuous (fun σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ =>
      (Units.map (LinearMap.toMatrixAlgEquiv b).toMonoidHom (ρ.ρ.toHomUnits σ) :
        GL (Fin 2) A)) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_continuous_unitsMap_toMatrix_of_isAdicContinuous.solution

#print axioms GaloisRepAdic.continuous_unitsMap_toMatrix_of_isAdicContinuous

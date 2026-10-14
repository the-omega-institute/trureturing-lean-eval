import Submission.Supplier.Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Submission.Supplier.Definitions.Def_HeckeCharacter_FiniteOrder
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_AutomorphicForm_SmoothCuspRealizationAt_isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open IsDedekindDomain NumberField
theorem AutomorphicForm.SmoothCuspRealizationAt.isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (B : Set (AdeleRing (𝓞 F) F)) (Φ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F
      (productionPinsOf F D (fun N => NumberField.AdelicLevel.levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        gen B) Φ) :
    IsIdeleClassChar (𝓞 F) F (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) ∧
      HeckeCharacter.AdmitsModulus F (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) Φ.level ∧
      (IsGenuineCuspRealizationAt F
          (productionPinsOf F D (fun N => NumberField.AdelicLevel.levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
            gen B) Φ R →
        Continuous (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine.solution

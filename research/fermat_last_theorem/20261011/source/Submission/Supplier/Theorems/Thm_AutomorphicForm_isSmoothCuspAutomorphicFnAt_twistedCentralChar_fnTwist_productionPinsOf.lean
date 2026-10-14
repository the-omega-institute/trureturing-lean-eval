import Submission.Supplier.Definitions.Def_AutomorphicForm_CuspidalConstituent
import Submission.Supplier.Definitions.Def_AutomorphicForm_FnTwist
import Submission.Supplier.Definitions.Def_HeckeCharacter_FiniteOrder
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_AutomorphicForm_isSmoothCuspAutomorphicFnAt_twistedCentralChar_fnTwist_productionPinsOf

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open AutomorphicForm

theorem AutomorphicForm.isSmoothCuspAutomorphicFnAt_twistedCentralChar_fnTwist_productionPinsOf
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F) (B : Set (AdeleRing (𝓞 F) F))
    (ξ : (productionPinsOf F D U gen B).Z →* ℂˣ)
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hη : HeckeCharacter.IsFiniteOrderHeckeChar F η)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsSmoothCuspAutomorphicFnAt F (productionPinsOf F D U gen B) ξ φ) :
    IsSmoothCuspAutomorphicFnAt F (productionPinsOf F D U gen B) (twistedCentralChar F _ ξ η) (fnTwist F η φ) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isSmoothCuspAutomorphicFnAt_twistedCentralChar_fnTwist_productionPinsOf.solution

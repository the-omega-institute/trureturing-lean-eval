import Submission.Supplier.Definitions.Def_AutomorphicForm_CuspidalConstituent
import Submission.Supplier.Definitions.Def_AutomorphicForm_FnTwist
import Submission.Supplier.Definitions.Def_HeckeCharacter_FiniteOrder
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_AutomorphicForm_CuspidalConstituent_isCuspConstituent_twistedCentralChar_span_image_fnTwist

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open AutomorphicForm AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.isCuspConstituent_twistedCentralChar_span_image_fnTwist
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F) (B : Set (AdeleRing (𝓞 F) F))
    (ξ : (productionPinsOf F D U gen B).Z →* ℂˣ)
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hη : HeckeCharacter.IsFiniteOrderHeckeChar F η)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hV : IsCuspConstituent F (productionPinsOf F D U gen B) ξ V) :
    IsCuspConstituent F (productionPinsOf F D U gen B) (twistedCentralChar F _ ξ η)
      (Submodule.span ℂ ((fun φ => fnTwist F η φ) '' (V : Set (AdelicGL2 (𝓞 F) F → ℂ)))) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_CuspidalConstituent_isCuspConstituent_twistedCentralChar_span_image_fnTwist.solution

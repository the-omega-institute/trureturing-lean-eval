import Submission.Supplier.Definitions.Def_M4aHerbrand_IdeleClassVocab
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_NumberField_AdeleRing_exists_isOpen_inter_principalIdeles_eq_singleton

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open NumberField

theorem NumberField.AdeleRing.exists_isOpen_inter_principalIdeles_eq_singleton
    (F : Type) [Field F] [NumberField F] :
    ∃ V : Set (AdeleRing (𝓞 F) F)ˣ, IsOpen V ∧
      V ∩ (M4aHerbrand.principalIdeles (𝓞 F) F : Set (AdeleRing (𝓞 F) F)ˣ) = {1} := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdeleRing_exists_isOpen_inter_principalIdeles_eq_singleton.solution

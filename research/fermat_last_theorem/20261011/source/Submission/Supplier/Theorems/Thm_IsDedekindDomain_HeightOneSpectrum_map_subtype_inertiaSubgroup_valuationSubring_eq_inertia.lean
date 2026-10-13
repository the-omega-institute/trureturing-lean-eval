import Mathlib
import Submission.Supplier.Definitions.Def_NumberField_PlaceDecompositionAction
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_IsDedekindDomain_HeightOneSpectrum_map_subtype_inertiaSubgroup_valuationSubring_eq_inertia

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField.PlaceDecomp

theorem IsDedekindDomain.HeightOneSpectrum.map_subtype_inertiaSubgroup_valuationSubring_eq_inertia
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]
    (w : HeightOneSpectrum (𝓞 F)) :
    (((w.valuation F).valuationSubring).inertiaSubgroup E).map
        (((w.valuation F).valuationSubring).decompositionSubgroup E).subtype =
      w.asIdeal.inertia (F ≃ₐ[E] F) := by p2m_exact_reverting @_root_.P2MW.S_IsDedekindDomain_HeightOneSpectrum_map_subtype_inertiaSubgroup_valuationSubring_eq_inertia.solution

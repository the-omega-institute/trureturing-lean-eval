import Mathlib
import Submission.Supplier.Definitions.Def_Patching_SystemTypes
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_IsLocalRing_isRegular_of_systemOfParameters

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

open IsLocalRing RingTheory
theorem IsLocalRing.isRegular_of_systemOfParameters
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hCM : (Module.depth R R : WithBot ℕ∞) = ringKrullDim R)
    {d : ℕ} (hdim : ringKrullDim R = d)
    (xs : List R) (hlen : xs.length = d) (hmem : ∀ y ∈ xs, y ∈ maximalIdeal R)
    (hsop : ringKrullDim (R ⧸ Ideal.ofList xs) = 0) :
    RingTheory.Sequence.IsRegular R xs := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_isRegular_of_systemOfParameters.solution

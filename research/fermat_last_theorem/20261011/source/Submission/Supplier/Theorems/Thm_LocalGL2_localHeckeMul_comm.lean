import Mathlib
import Submission.Supplier.Definitions.Def_LocalLanglands_CartanDecomposition
import Submission.Supplier.Definitions.Def_LocalLanglands_HeckePair
import Submission.Supplier.Definitions.Def_LocalLanglands_GelfandInvolution
import Submission.Supplier.Definitions.Def_LocalLanglands_LocalHeckeInstance
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_LocalGL2_localHeckeMul_comm

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

open Matrix LocalGL2 HeckePair
theorem LocalGL2.localHeckeMul_comm
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {R₀ : Type*} [CommRing R₀]
    (f₁ f₂ : HeckePair.HeckeAlgebra (integralSubgroup R K) R₀) :
    f₁ * f₂ = f₂ * f₁ := by p2m_exact_reverting @_root_.P2MW.S_LocalGL2_localHeckeMul_comm.solution

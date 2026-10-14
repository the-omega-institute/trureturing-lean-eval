import Submission.Supplier.Definitions.Def_AlgebraicCurve_Differentials
import Submission.Supplier.P2M.Util

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
namespace P2MW.S_AlgebraicCurve_pullbackDiff_smul

set_option autoImplicit false

open AlgebraicCurve in

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] (φ : F →ₐ[K] F') (g : F) (ω : Ω[F⁄K]) :
    pullbackDiff φ (g • ω) = φ g • pullbackDiff φ ω := by
  letI : Algebra F F' := φ.toRingHom.toAlgebra
  haveI : IsScalarTower K F F' := IsScalarTower.of_algebraMap_eq fun k => (φ.commutes k).symm
  show (KaehlerDifferential.map K K F F') (g • ω) = φ g • (KaehlerDifferential.map K K F F') ω
  rw [map_smul]
  exact (algebraMap_smul F' g _).symm

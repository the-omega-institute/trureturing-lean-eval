import Submission.Supplier.Definitions.Def_WeierstrassCurve_ProjModel
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_WeierstrassProjModel_projModelStrCR_smoothOfRelativeDimension_one

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
attribute [-instance] WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType
attribute [-simp] WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X

open AlgebraicGeometry WeierstrassProjModel

universe u

theorem WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one
    {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R) [V.IsElliptic] :
    SmoothOfRelativeDimension 1 (projModelStrCR V) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_projModelStrCR_smoothOfRelativeDimension_one.solution

#print axioms WeierstrassProjModel.projModelStrCR_smoothOfRelativeDimension_one

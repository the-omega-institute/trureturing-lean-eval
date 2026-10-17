import Submission.Supplier.Definitions.Def_WeierstrassCurve_ProjModel
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.RingHom.Smooth
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_WeierstrassProjModel_projModelStrCR_smooth_of_zChartBridge_of_yChartSmooth

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

attribute [local instance] MvPolynomial.gradedAlgebra in
theorem WeierstrassProjModel.projModelStrCR_smooth_of_zChartBridge_of_yChartSmooth
    {R : Type} [CommRing R] (V : WeierstrassCurve.Projective R) [V.IsElliptic]
    (hbr : ∃ f : HomogeneousLocalization.Away (WeierstrassProjModel.projModelGradingCR V)
          (Ideal.Quotient.mk (WeierstrassProjModel.projModelHomogeneousIdealCR V).toIdeal
            (MvPolynomial.X 2 : MvPolynomial (Fin 3) R)) →+*
        (Polynomial (Polynomial R) ⧸ Ideal.span {V.toAffine.polynomial}),
      Function.Bijective f ∧
        f.comp ((HomogeneousLocalization.fromZeroRingHom
              (WeierstrassProjModel.projModelGradingCR V)
              (Submonoid.powers (Ideal.Quotient.mk
                (WeierstrassProjModel.projModelHomogeneousIdealCR V).toIdeal
                (MvPolynomial.X 2 : MvPolynomial (Fin 3) R)))).comp
            (algebraMap R (WeierstrassProjModel.projModelGradingCR V 0))) =
          algebraMap R (Polynomial (Polynomial R) ⧸ Ideal.span {V.toAffine.polynomial}))
    (hy : RingHom.Smooth ((HomogeneousLocalization.fromZeroRingHom
            (WeierstrassProjModel.projModelGradingCR V)
            (Submonoid.powers (Ideal.Quotient.mk
              (WeierstrassProjModel.projModelHomogeneousIdealCR V).toIdeal
              (MvPolynomial.X 1 : MvPolynomial (Fin 3) R)))).comp
          (algebraMap R (WeierstrassProjModel.projModelGradingCR V 0)))) :
    AlgebraicGeometry.Smooth (WeierstrassProjModel.projModelStrCR V) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_projModelStrCR_smooth_of_zChartBridge_of_yChartSmooth.solution

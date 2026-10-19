import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Submission.Supplier.Definitions.Def_AlgebraicCurve_CurveModel
import Submission.Supplier.Definitions.Def_AlgebraicCurve_Correspondence
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_AlgebraicCurve_CurveModel_exists_finite_flat_hom_of_algHom

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u v w

namespace AlgebraicCurve.CurveModel

theorem exists_finite_flat_hom_of_algHom {K : Type u} [Field K]
    {F : Type v} {F' : Type w} [Field F] [Algebra K F] [Field F'] [Algebra K F']
    (M : CurveModel K F) (M' : CurveModel K F')
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ) :
    ∃ π : M'.C ⟶ M.C,
      π ≫ M.toBase = M'.toBase ∧
      IsFinite π ∧ Flat π ∧ LocallyOfFinitePresentation π ∧
      (∀ x : M.C, π.finrank x = finrankAlong K φ) ∧
      M'.C.fromSpecStalk (genericPoint M'.C) ≫ π =
        Spec.map (CommRingCat.ofHom
          (M'.ffEquiv.toRingHom.comp (φ.toRingHom.comp M.ffEquiv.symm.toRingHom))) ≫
          M.C.fromSpecStalk (genericPoint M.C) ∧
      (∀ y : closedPoints M'.C, ∃ h : π.base y.1 ∈ closedPoints M.C,
        M.placeOfPoint ⟨π.base y.1, h⟩ = (M'.placeOfPoint y).restrictAlong φ hφ) ∧
      ∀ π' : M'.C ⟶ M.C,
        M'.C.fromSpecStalk (genericPoint M'.C) ≫ π' =
          M'.C.fromSpecStalk (genericPoint M'.C) ≫ π → π' = π := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_CurveModel_exists_finite_flat_hom_of_algHom.solution

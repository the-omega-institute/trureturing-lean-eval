import Mathlib
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_ValuationSubring_exists_algEquiv_smul_eq_and_residue_eq_of_ringEquiv_residueField

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.
attribute [-instance] instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv
attribute [-simp] FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq

open scoped Pointwise in
theorem ValuationSubring.exists_algEquiv_smul_eq_and_residue_eq_of_ringEquiv_residueField (p : ℕ) [Fact p.Prime] (A A' : ValuationSubring (AlgebraicClosure ℚ)) [CharP (IsLocalRing.ResidueField A) p] (e : IsLocalRing.ResidueField A' ≃+* IsLocalRing.ResidueField A) : ∃ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, τ • A' = A ∧ ∀ (x : A') (y : A), (y : AlgebraicClosure ℚ) = τ (x : AlgebraicClosure ℚ) → IsLocalRing.residue A y = e (IsLocalRing.residue A' x) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_algEquiv_smul_eq_and_residue_eq_of_ringEquiv_residueField.solution

#print axioms ValuationSubring.exists_algEquiv_smul_eq_and_residue_eq_of_ringEquiv_residueField

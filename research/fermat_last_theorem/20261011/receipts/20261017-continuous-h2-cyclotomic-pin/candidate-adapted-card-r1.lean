import Mathlib
import Submission.Supplier.Definitions.Def_GroupCohomology_ContinuousUnramified
import Submission.Supplier.Definitions.Def_DualSelmer_ExtConditions
import Submission.Supplier.Definitions.Def_ExtCitation_KummerBridge
import Submission.Supplier.Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Submission.Supplier.Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Submission.Supplier.Definitions.Def_NumberField_LevelArithmeticModP
import Submission.Supplier.Definitions.Def_NumberField_SelmerRepModP
import Submission.Supplier.Definitions.Def_Rep_QuotientRightTranslation
import Submission.Supplier.Definitions.Def_GroupCohomology_CyclotomicQuotientH2Rep
import Submission.Supplier.P2M.Util
import Submission.Supplier.P2M.Sol.S_groupCohomology_exists_continuousH2Sr_cyclotomicQuotientRep_equiv_pin

-- Elaborator settings from the recovered exact-pin FLT controller.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option debug.skipKernelTC false
-- End recovered elaborator settings.

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MonoidalCategory Module groupCohomology ExtCitation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private local instance scalarAddCommGroup (p : ℕ) : AddCommGroup (ZMod p) :=
  (inferInstance : CommRing (ZMod p)).toAddCommGroup

theorem groupCohomology.exists_continuousH2Sr_cyclotomicQuotientRep_equiv_pin
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKL : K ≤ L) (hL : L.IsUnramifiedOutside S)
    [(L.fixingSubgroup.subgroupOf K.fixingSubgroup).Normal] [(L.fixingSubgroup.subgroupOf K.fixingSubgroup).FiniteIndex] :
    ∃ Θ : continuousH2Sr K.fixingSubgroup.subtype S (cyclotomicQuotientRep K L p) ≃ₗ[ZMod p]
        continuousH2Sr L.fixingSubgroup.subtype S
          ((Rep.trivial (ZMod p) ↥L.fixingSubgroup (ZMod p)).twist ((cycloChar p).comp L.fixingSubgroup.subtype)),
      (∀ (z : ↥(levelCocyclesSr₂ K.fixingSubgroup.subtype S (cyclotomicQuotientRep K L p)))
          (w : ↥(levelCocyclesSr₂ L.fixingSubgroup.subtype S
            ((Rep.trivial (ZMod p) ↥L.fixingSubgroup (ZMod p)).twist ((cycloChar p).comp L.fixingSubgroup.subtype)))),
        (∀ s t : ↥L.fixingSubgroup,
            (w : ↥L.fixingSubgroup × ↥L.fixingSubgroup → ZMod p) (s, t) =
              ((z : ↥K.fixingSubgroup × ↥K.fixingSubgroup → (↥K.fixingSubgroup ⧸ L.fixingSubgroup.subgroupOf K.fixingSubgroup) →₀ ZMod p)
                (⟨(s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), IntermediateField.fixingSubgroup_antitone hKL s.2⟩,
                 ⟨(t : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), IntermediateField.fixingSubgroup_antitone hKL t.2⟩))
                (1 : ↥K.fixingSubgroup ⧸ L.fixingSubgroup.subgroupOf K.fixingSubgroup)) →
          Θ (continuousH2Srπ K.fixingSubgroup.subtype S _ z) = continuousH2Srπ L.fixingSubgroup.subtype S _ w) ∧
      ∀ (σ : ↥K.fixingSubgroup) (a : continuousH2Sr K.fixingSubgroup.subtype S (cyclotomicQuotientRep K L p))
        (w w' : ↥(levelCocyclesSr₂ L.fixingSubgroup.subtype S
          ((Rep.trivial (ZMod p) ↥L.fixingSubgroup (ZMod p)).twist ((cycloChar p).comp L.fixingSubgroup.subtype)))),
        Θ a = continuousH2Srπ L.fixingSubgroup.subtype S _ w →
        (∀ s t s' t' : ↥L.fixingSubgroup,
            ((σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))⁻¹ * s * σ = s' →
            ((σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))⁻¹ * t * σ = t' →
              (w' : ↥L.fixingSubgroup × ↥L.fixingSubgroup → ZMod p) (s, t) =
                ((cycloChar p (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : (ZMod p)ˣ) : ZMod p) *
                  (w : ↥L.fixingSubgroup × ↥L.fixingSubgroup → ZMod p) (s', t')) →
          Θ (continuousH2SrMapHom S K.fixingSubgroup.subtype (cyclotomicQuotientRT K L p σ) a) =
            continuousH2Srπ L.fixingSubgroup.subtype S _ w' := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_continuousH2Sr_cyclotomicQuotientRep_equiv_pin.solution

#print axioms groupCohomology.exists_continuousH2Sr_cyclotomicQuotientRep_equiv_pin
